open! Core
open! Syntax
open! Rich_wasm
open! Annotated
open Or_error.Let_syntax

let rec compile_size (s : Annotated.Size.t) : Rich_wasm.Size.t =
  match s with
  | Const i -> SizeC i
  | Var i -> SizeV i
  | Plus (s1, s2) -> SizeP (compile_size s1, compile_size s2)
;;

let compile_qual (q : Annotated.Qual.t) : Rich_wasm.Qual.t =
  match q with
  | Unr -> QualC Unr
  | Lin -> QualC Lin
;;

let compile_abstraction (a : Annotated.Abstraction.t) : KindVar.t =
  match a with
  | Size -> Size ([], [])
  | Type (q, s) -> Type (compile_qual q, compile_size s, Heapable)
;;

let rec compile_pretype (pt : Annotated.Pretype.t) (q_expansion : Rich_wasm.Qual.t)
  : Rich_wasm.Type.pt
  =
  let open Rich_wasm.Type in
  match pt with
  | Int -> Num (Int (S, I32))
  | Var i -> Var i
  | Unit -> Unit
  | Exists_closure { foralls; args; ret } ->
    let foralls = List.map ~f:compile_abstraction foralls in
    let args = List.map ~f:compile_type args in
    let ret = compile_type ret in
    let unr = Rich_wasm.(Qual.QualC Qual_const.Unr) in
    let sz = Rich_wasm.Size.SizeC 64 in
    let only_type_abstractions = function
      | KindVar.Size _ | Qual _ | Loc -> false
      | Type _ -> true
    in
    let var =
      ( Rich_wasm.Type.Var
          (foralls |> List.filter ~f:only_type_abstractions |> List.length)
      , unr )
    in
    ExLoc
      ( Rich_wasm.Type.Ref
          ( Rich_wasm.Cap.W
          , LocV 0
          , Ex
              ( unr
              , sz
              , ( Prod
                    [ Var 0, unr; Coderef (foralls, (var :: args, [ ret ])), q_expansion ]
                , q_expansion ) ) )
      , unr )
  | Ref (sz, t) ->
    let sz = compile_size sz in
    let pt, qual = compile_type t in
    (match q_expansion, qual with
     | QualC Unr, QualC Unr | QualC Lin, _ ->
       ExLoc (Ref (W, LocV 0, Struct [ (pt, qual), sz ]), q_expansion)
     | QualC Unr, QualC Lin ->
       ExLoc
         ( Ref
             ( W
             , LocV 0
             , Struct
                 [ ( ( ExLoc
                         ( Ref (W, LocV 0, Variant [ Unit, QualC Unr; pt, qual ])
                         , QualC Lin )
                     , QualC Lin )
                   , SizeC 64 )
                 ] )
         , q_expansion )
     | QualV _, _ | _, QualV _ ->
       raise_s [%message "BUG: code generation ecountered qual variable"])
  | Variant ts ->
    let ts = List.map ~f:compile_type ts in
    ExLoc
      ( Rich_wasm.Type.Ref (Rich_wasm.Cap.W, LocV 0, Variant ts)
      , Rich_wasm.(Qual.QualC Qual_const.Unr) )
  | Prod ts ->
    let ts = List.map ~f:compile_type ts in
    Prod ts
  | Rec (q, t) -> Rec (compile_qual q, compile_type t)

and compile_type (Info (_, (q, pt)) : Annotated.Type.t) : Rich_wasm.Type.t =
  let q = compile_qual q in
  let pt = compile_pretype pt q in
  pt, q
;;

module Local_env : sig
  type t [@@deriving sexp]

  val create : num_arg_locals:int -> t
  val bind_arg : int -> t -> t
  val bind : Annotated.Size.t -> t -> t
  val unbind_exn : t -> t
  val find_exn : int -> t -> int
  val to_list : t -> Annotated.Size.t list
end = struct
  type t =
    { debruijn_to_local : int list
    ; locals : Annotated.Size.t list
    ; num_arg_locals : int
    }
  [@@deriving sexp]

  let create ~num_arg_locals =
    { debruijn_to_local = []
    ; locals = List.init num_arg_locals ~f:(fun _ -> Annotated.Size.Const 0)
    ; num_arg_locals
    }
  ;;

  let bind_arg idx t = { t with debruijn_to_local = idx :: t.debruijn_to_local }

  let bind s t =
    let idx = List.length t.locals in
    let locals = t.locals @ [ s ] in
    let debruijn_to_local = idx :: t.debruijn_to_local in
    { debruijn_to_local; locals; num_arg_locals = t.num_arg_locals }
  ;;

  let unbind_exn t = { t with debruijn_to_local = List.tl_exn t.debruijn_to_local }
  let find_exn i t = List.nth_exn t.debruijn_to_local i
  let to_list t = List.drop t.locals t.num_arg_locals
end

module Size_env : sig
  type t

  val empty : t
  val add : Annotated.Size.t -> t -> t
  val find_exn : int -> t -> Annotated.Size.t
end = struct
  type t = Annotated.Size.t list

  let empty = []
  let add e t = e :: t
  let find_exn i t = List.nth_exn t i
end

let rec type_size (Info (_, (_, t)) : Annotated.Type.t) (gamma : Size_env.t)
  : Annotated.Size.t
  =
  let open Annotated.Size in
  match t with
  | Int -> Const 32
  | Var n -> Size_env.find_exn n gamma
  | Unit -> Const 0
  | Exists_closure _ -> Const 64
  | Ref (_, _) -> Const 64
  | Variant _ -> Const 64
  | Prod ts ->
    List.fold ~init:(Const 0) ~f:(fun acc t -> Plus (acc, type_size t gamma)) ts
  | Rec (_, t) -> type_size t (Size_env.add (Const (-1)) gamma)
;;

let compile_expr e alpha_sizes local_env : Rich_wasm.Instruction.t list * Local_env.t =
  let rec h_e (Info { tag = _; typ; e } : Annotated.Expr.t) local_env ~alpha_sizes
    : Rich_wasm.Instruction.t list * Local_env.t * Rich_wasm.LocalEffect.t
    =
    let h = h_e ~alpha_sizes in
    let open Rich_wasm.Instruction in
    match e with
    | Int i -> [ IVal (Num (Int (S, I32), Second (Int32.of_int_exn i))) ], local_env, []
    | Binop (e1, e2, op) ->
      let op =
        match op with
        | `Add -> Rich_wasm.IBinOp.Iadd
        | `Sub -> Isub
        | `Mul -> Imul
        | `Div -> Idiv S
      in
      let e2, local_env, le1 = h e2 local_env in
      let e1, local_env, le2 = h e1 local_env in
      e2 @ e1 @ [ INe (Ib (I32, op)) ], local_env, le1 @ le2
    | If0 (e1, e2, e3) ->
      let typ =
        match e2 with
        | Info { typ; _ } -> typ
      in
      let e1, local_env, le1 = h e1 local_env in
      let e2, local_env, le2 = h e2 local_env in
      let e3, local_env, le3 = h e3 local_env in
      ( e1
        @ [ INe (CvtI (I32, IConvert (I32, U)))
          ; IITE (([], [ compile_type typ ]), le2 @ le3, e2, e3)
          ]
      , local_env
      , le1 @ le2 @ le3 )
    | Let { var; bind; body } ->
      let (Info { typ = bind_typ; _ }) = bind in
      let bind_size = type_size bind_typ alpha_sizes in
      let bind, local_env, le_bind = h bind local_env in
      (match var with
       | Unit ->
         let body, local_env, le_body = h_e body local_env ~alpha_sizes in
         bind @ [ IDrop ] @ body, local_env, le_bind @ le_body
       | Variable ->
         let local_env = Local_env.bind bind_size local_env in
         let local = Local_env.find_exn 0 local_env in
         let body, local_env, le_body = h_e body local_env ~alpha_sizes in
         ( bind @ [ ISet_local local ] @ body @ [ IVal Unit; ISet_local local ]
         , Local_env.unbind_exn local_env
         , le_bind @ le_body )
       | Tuple n ->
         let typs =
           match (bind_typ : Annotated.Type.t) with
           | Info (_, (_, Prod typs)) when List.length typs = n -> typs
           | _ ->
             raise_s
               [%message
                 "BUG: tuple pattern for non-tuple (with right size) type during code \
                  generation"
                   (bind_typ : Annotated.Type.t)
                   (n : int)]
         in
         let local_env, sets, unsets =
           List.fold_left
             typs
             ~init:(local_env, [], [])
             ~f:(fun (local_env, sets, unsets) typ ->
               let size = type_size typ alpha_sizes in
               let local_env = Local_env.bind size local_env in
               let idx = Local_env.find_exn 0 local_env in
               ( local_env
               , [ Instruction.ISet_local idx ] @ sets
               , [ Instruction.IVal Unit; ISet_local idx ] @ unsets ))
         in
         let body, local_env, le_body = h_e body local_env ~alpha_sizes in
         let local_env =
           List.fold
             (List.init n ~f:(Fn.const ()))
             ~init:local_env
             ~f:(fun local_env () -> Local_env.unbind_exn local_env)
         in
         bind @ [ IUngroup ] @ sets @ body @ unsets, local_env, le_bind @ le_body)
    | Var n ->
      let (Info (_, (qual, _))) = typ in
      let local = Local_env.find_exn n local_env in
      let le =
        match qual with
        | Unr -> []
        | Lin -> [ local, ((Unit, QualC Unr) : Rich_wasm.Type.t) ]
      in
      [ IGet_local (local, compile_qual qual) ], local_env, le
    | Global n -> [ IGet_global n ], local_env, []
    | Unit -> [ IVal Unit ], local_env, []
    | Coderef { f; env; type_insts } ->
      let insts =
        List.concat_map
          ~f:(fun (Info (_, (q, pt)) as typ) ->
            let size = type_size typ alpha_sizes in
            [ Rich_wasm.Index.SizeI (compile_size size)
            ; PretypeI (compile_pretype pt (compile_qual q))
            ])
          type_insts
      in
      let package_typ = typ in
      (match package_typ with
       | Info (_, (q_fun, Exists_closure { foralls; args; ret })) ->
         let foralls = List.map ~f:compile_abstraction foralls in
         let args = List.map ~f:compile_type args in
         let ret = compile_type ret in
         let (Info { tag = _; typ = env_typ; e = _ }) = env in
         let env_typ = compile_type env_typ |> fst in
         let env, local_env, le = h env local_env in
         let only_type_abstractions = function
           | KindVar.Size _ | Qual _ | Loc -> false
           | Type _ -> true
         in
         let var =
           ( Rich_wasm.Type.Var
               (foralls |> List.filter ~f:only_type_abstractions |> List.length)
           , Rich_wasm.Qual.QualC Unr )
         in
         ( env
           @ [ ICoderefI f; IInst insts ]
           @ [ IGroup (2, QualC Qual_const.Unr)
             ; IExistPack
                 ( env_typ
                 , Ex
                     ( QualC Qual_const.Unr
                     , SizeC 64
                     , ( Prod
                           [ Var 0, QualC Qual_const.Unr
                           ; Coderef (foralls, (var :: args, [ ret ])), compile_qual q_fun
                           ]
                       , compile_qual q_fun ) )
                 , QualC Qual_const.Unr )
             ]
         , local_env
         , le )
       | _ -> raise_s [%message "BUG: codegen calling pack of non closure"])
    | Apply { f; inst; args } ->
      let f, local_env, le_f = h f local_env in
      let inst =
        List.map inst ~f:(fun (sz, t) ->
          [ Rich_wasm.Index.SizeI (compile_size sz)
          ; Rich_wasm.Index.PretypeI (compile_type t |> fst)
          ])
        |> List.concat
      in
      let (local_env, le_args), args =
        let alpha_sizes = Size_env.add (Const 64) alpha_sizes in
        List.fold_map args ~init:(local_env, []) ~f:(fun (local_env, le) arg ->
          let arg, local_env, le_arg = h_e arg local_env ~alpha_sizes in
          (local_env, le @ le_arg), arg)
      in
      let args = List.concat args in
      let local_env = Local_env.bind (Const 64) local_env in
      let local = Local_env.find_exn 0 local_env in
      let local_env = Local_env.unbind_exn local_env in
      let drop_instructions, local_env =
        let typ_size = type_size typ alpha_sizes in
        let local_env = Local_env.bind typ_size local_env in
        let local = Local_env.find_exn 0 local_env in
        let local_env = Local_env.unbind_exn local_env in
        let (Info (_, (ret_qual, _))) = typ in
        ( [ ISet_local local
          ; IDrop
          ; IGet_local (local, compile_qual ret_qual)
          ; IVal Unit
          ; ISet_local local
          ]
        , local_env )
      in
      ( f
        @ [ IMemUnpack
              ( ([], [ compile_type typ ])
              , le_args
              , [ IExistUnpack
                    ( QualC Qual_const.Unr
                    , ([], [ compile_type typ ])
                    , le_args
                    , [ IUngroup; ISet_local local ]
                      @ args
                      @ [ IGet_local (local, QualC Qual_const.Unr)
                        ; IInst inst
                        ; ICall_indirect
                        ; IVal Unit
                        ; ISet_local local
                        ] )
                ]
                @ drop_instructions )
          ]
      , local_env
      , le_f @ le_args )
    | New e ->
      let (Info { typ = e_typ; _ }) = e in
      let e_size = type_size e_typ alpha_sizes |> compile_size in
      let e, local_env, le = h e local_env in
      ( e @ [ IStructMalloc ([ e_size ], Rich_wasm.(Qual.QualC Qual_const.Unr)) ]
      , local_env
      , le )
    | New_lin typ ->
      let typ = compile_type typ in
      ( [ IVal Unit
        ; IVariantMalloc (0, [ Unit, QualC Unr; typ ], QualC Lin)
        ; IStructMalloc ([ SizeC 64 ], QualC Unr)
        ]
      , local_env
      , [] )
    | Deref e ->
      let e_typ =
        let (Info { typ = e_typ; _ }) = e in
        match e_typ with
        | Info (_, (_, Ref (_, e_typ))) -> e_typ
        | _ -> raise_s [%message "BUG: codegen called for deref of non-reference"]
      in
      let (Info (_, (e_qual, _))) = e_typ in
      let (Info (_, (qual, _))) = typ in
      let size = type_size typ alpha_sizes in
      let typ = compile_type typ in
      let e, local_env, le = h e local_env in
      let local_env = Local_env.bind size local_env in
      let local = Local_env.find_exn 0 local_env in
      let local_env = Local_env.unbind_exn local_env in
      (match e_qual with
       | Unr ->
         ( e
           @ [ IMemUnpack
                 ( ([], [ typ ])
                 , []
                 , [ IStructGet 0
                   ; ISet_local local
                   ; IDrop
                   ; IGet_local (local, compile_qual qual)
                   ; IVal Unit
                   ; ISet_local local
                   ] )
             ]
         , local_env
         , le )
       | Lin ->
         ( e
           @ [ IMemUnpack
                 ( ([], [])
                 , [ local, typ ]
                 , [ IVal Unit
                   ; IVariantMalloc (0, [ Unit, QualC Unr; typ ], QualC Lin)
                   ; IStructSwap 0
                   ; IMemUnpack
                       ( ([], [])
                       , [ local, typ ]
                       , [ IVariantCase
                             ( QualC Lin
                             , ([], [])
                             , [ local, typ ]
                             , [ [ IUnreachable ]; [ ISet_local local ] ] )
                         ] )
                   ; IDrop
                   ] )
             ; IGet_local (local, compile_qual qual)
             ; IVal Unit
             ; ISet_local local
             ]
         , local_env
         , le ))
    | Assign { ref; value } ->
      let (Info { typ = value_typ; _ }) = value in
      let (Info (_, (value_qual, _))) = value_typ in
      let ref, local_env, le_ref = h ref local_env in
      let value, local_env, le_val = h value local_env in
      let typ = compile_type typ in
      let value_typ = compile_type value_typ in
      (match value_qual with
       | Unr ->
         ( ref
           @ [ IMemUnpack
                 (([], [ typ ]), le_val, value @ [ IStructSet 0; IDrop; IVal Unit ])
             ]
         , local_env
         , le_ref @ le_val )
       | Lin ->
         ( ref
           @ [ IMemUnpack
                 ( ([], [ typ ])
                 , le_val
                 , value
                   @ [ IVariantMalloc (1, [ Unit, QualC Unr; value_typ ], QualC Lin)
                     ; IStructSwap 0
                     ; IMemUnpack
                         ( ([], [])
                         , []
                         , [ IVariantCase
                               (QualC Lin, ([], []), [], [ [ IDrop ]; [ IUnreachable ] ])
                           ] )
                     ; IDrop
                     ; IVal Unit
                     ] )
             ]
         , local_env
         , le_ref @ le_val ))
    | Inj { n; typ; value } ->
      let typ = List.map ~f:compile_type typ in
      let value, local_env, le = h value local_env in
      ( value @ [ IVariantMalloc (n, typ, Rich_wasm.(Qual.QualC Qual_const.Unr)) ]
      , local_env
      , le )
    | Case { bind; body } ->
      let (Info { typ = bind_typ; _ }) = bind in
      let (Info (_, (variant_qual, _))) = bind_typ in
      let inner_typs =
        match bind_typ with
        | Info (_, (_, Variant typs)) -> typs
        | _ -> raise_s [%message "BUG: codegen called for case of non-variant"]
      in
      let bind, local_env, le_bind = h bind local_env in
      let (local_env, le_body), body =
        List.fold_map
          (List.zip_exn body inner_typs)
          ~init:(local_env, [])
          ~f:(fun (local_env, le) (t, typ) ->
            let typ_size = type_size typ alpha_sizes in
            let local_env = Local_env.bind typ_size local_env in
            let local = Local_env.find_exn 0 local_env in
            let t, local_env, le_t = h t local_env in
            let local_env = Local_env.unbind_exn local_env in
            ( (local_env, le @ le_t)
            , (ISet_local local :: t) @ [ IVal Unit; ISet_local local ] ))
      in
      let drop_instructions, local_env =
        match variant_qual with
        | Lin -> [], local_env
        | Unr ->
          let typ_size = type_size typ alpha_sizes in
          let local_env = Local_env.bind typ_size local_env in
          let local = Local_env.find_exn 0 local_env in
          let local_env = Local_env.unbind_exn local_env in
          let (Info (_, (ret_qual, _))) = typ in
          ( [ ISet_local local
            ; IDrop
            ; IGet_local (local, compile_qual ret_qual)
            ; IVal Unit
            ; ISet_local local
            ]
          , local_env )
      in
      let typ = compile_type typ in
      let at = [], [ typ ] in
      ( bind
        @ [ IMemUnpack
              ( at
              , le_body
              , [ IVariantCase (compile_qual variant_qual, at, le_body, body) ]
                @ drop_instructions )
          ]
      , local_env
      , le_bind @ le_body )
    | Prod ts ->
      let (Info (_, (qual, _))) = typ in
      let (local_env, le), ts =
        List.fold_map ts ~init:(local_env, []) ~f:(fun (local_env, le) t ->
          let t, local_env, le_t = h t local_env in
          (local_env, le @ le_t), t)
      in
      List.concat ts @ [ IGroup (List.length ts, compile_qual qual) ], local_env, le
    | Proj { e; n } ->
      let (Info { tag = _; typ; e = _ }) = e in
      let (Info (_, (_, pt))) = typ in
      let e, local_env, le = h e local_env in
      (match pt with
       | Prod ts ->
         let t = List.nth_exn ts n in
         let (Info (_, (qual, _))) = t in
         let t_size = type_size t alpha_sizes in
         let local_env = Local_env.bind t_size local_env in
         let local = Local_env.find_exn 0 local_env in
         let local_env = Local_env.unbind_exn local_env in
         ( e
           @ [ IUngroup ]
           @ List.init (List.length ts - (n + 1)) ~f:(fun _ -> IDrop)
           @ [ ISet_local local ]
           @ List.init n ~f:(fun _ -> IDrop)
           @ [ IGet_local (local, compile_qual qual); IVal Unit; ISet_local local ]
         , local_env
         , le )
       | _ ->
         raise_s
           [%message
             "violation of internal compiler invariant (proj from non product in codegen)"])
    | Fold { typ; e } ->
      let e, local_env, le = h e local_env in
      let (Info (_, (q, pt))) = typ in
      let pt = compile_pretype pt (compile_qual q) in
      e @ [ IRecFold pt ], local_env, le
    | Unfold e ->
      let e, local_env, le = h e local_env in
      e @ [ IRecUnfold ], local_env, le
  in
  let instrs, local_env, _ = h_e e local_env ~alpha_sizes in
  instrs, local_env
;;

(*
   | Inst (ts, e) ->
      let e, local_sizes = h e alpha_sizes local_sizes local_env ~depth in
      let ts =
        List.concat_map ts ~f:(fun (t_size, t) ->
            let t_size = compile_size t_size in
            let (Info (_, (q, pt))) = t in
            let q = compile_qual q in
            let pt = compile_pretype pt q in
            [ Rich_wasm.Index.SizeI t_size; QualI q; PretypeI pt ])
      in
      e @ [ IInst ts ], local_sizes
    | InstQ (qs, e) ->
      let e, local_sizes = h e alpha_sizes local_sizes local_env ~depth in
      let qs = List.map qs ~f:(fun q -> Rich_wasm.Index.QualI (compile_qual q)) in
      e @ [ IInst qs ], local_sizes
    | Apply { f; inst; inst_quals; args } ->
      let local_sizes, args =
        List.fold_map args ~init:local_sizes ~f:(fun local_sizes t ->
            let t, local_sizes = h t alpha_sizes local_sizes local_env ~depth in
            local_sizes, t)
      in
      let inst =
        List.concat_map inst ~f:(fun (t_size, t) ->
            let t_size = compile_size t_size in
            let (Info (_, (q, pt))) = t in
            let q = compile_qual q in
            let pt = compile_pretype pt q in
            [ Rich_wasm.Index.SizeI t_size; QualI q; PretypeI pt ])
      in
      let inst_quals =
        List.map inst_quals ~f:(fun q -> Rich_wasm.Index.QualI (compile_qual q))
      in
      let f, local_sizes = h f alpha_sizes local_sizes local_env ~depth in
      List.join args @ f @ [ IInst (inst @ inst_quals); ICall_indirect ], local_sizes
    | Unpack { package; body } ->
      let package, local_sizes = h package alpha_sizes local_sizes local_env ~depth in
      let pre_size = SizeEnv.size local_sizes in
      let body, local_sizes =
        h body alpha_sizes local_sizes local_env ~depth:(depth + 1)
      in
      let post_size = SizeEnv.size local_sizes in
      let typ = compile_type typ in
      let local_effect =
        List.map (List.range pre_size post_size) ~f:(fun i ->
            i, (Rich_wasm.Type.Unit, Rich_wasm.(Qual.QualC QualConst.Unr)))
      in
      let clear_locals =
        List.concat_map (List.range pre_size post_size) ~f:(fun i ->
            [ IVal Rich_wasm.Value.Unit; ISet_local i ])
      in
      let at = [], [ typ ] in
      ( package
        @ [ IMemUnpack
              ( at
              , local_effect
              , [ IExistUnpack
                    ( Rich_wasm.(Qual.QualC QualConst.Unr)
                    , at
                    , local_effect
                    , body @ clear_locals )
                ] )
          ]
      , local_sizes )
  in
  let e, local_sizes_rev = h e alpha_sizes (SizeEnv.init num_args) LocalEnv.empty ~depth in
  let local_sizes = local_sizes_rev |> SizeEnv.to_list |> List.rev_map ~f:compile_size in
  e, local_sizes
;;
*)

let size_env_of_foralls (foralls : Annotated.Abstraction.t list) : Size_env.t =
  let rec h foralls acc =
    let open Annotated.Abstraction in
    match foralls with
    | [] -> acc
    | Size :: rest -> h rest acc
    | Type (_, sz) :: rest -> h rest (Size_env.add sz acc)
  in
  h foralls Size_env.empty
;;

let local_env_of_arg_patterns patterns alpha_sizes =
  List.foldi
    patterns
    ~init:(Local_env.create ~num_arg_locals:(List.length patterns), [])
    ~f:(fun i (local_env, instructions) (pattern, typ) ->
      match (pattern : Annotated.Pattern_binding.t) with
      | Unit -> local_env, instructions
      | Variable -> Local_env.bind_arg i local_env, instructions
      | Tuple n ->
        let (Annotated.Type.Info (_, (qual, _))) = typ in
        let typs =
          match (typ : Annotated.Type.t) with
          | Info (_, (_, Prod typs)) when List.length typs = n -> typs
          | _ ->
            raise_s
              [%message
                "BUG: tuple pattern for non-tuple (with right size) type during code \
                 generation"]
        in
        let local_env, sets =
          List.fold_left typs ~init:(local_env, []) ~f:(fun (local_env, sets) typ ->
            let size = type_size typ alpha_sizes in
            let local_env = Local_env.bind size local_env in
            let idx = Local_env.find_exn 0 local_env in
            local_env, sets @ [ Instruction.ISet_local idx ])
        in
        local_env, [ Instruction.IGet_local (i, compile_qual qual); IUngroup ] @ sets)
;;

let codegen (m : Annotated.Module.t) ~source_printer : Rich_wasm.Module.t Or_error.t =
  let rec h m : (Instruction.f list * Glob.t list) Or_error.t =
    match (m : Module.t) with
    | LetIm ({ typ = { foralls; args; ret }; mod_name; fun_name }, m, _) ->
      let foralls = List.map ~f:compile_abstraction foralls in
      let args = List.map ~f:compile_type args in
      let ret = compile_type ret in
      let%bind rest_funs, rest_globs = h m in
      return
        ( Instruction.FunIm ([], (foralls, (args, [ ret ])), Import (mod_name, fun_name))
          :: rest_funs
        , rest_globs )
    | LetEx (name, { foralls; args; ret; body }, m, _) ->
      let patterns = args in
      let args = args |> List.map ~f:snd |> List.map ~f:compile_type in
      let ret = compile_type ret in
      let alpha_sizes = size_env_of_foralls foralls in
      let local_env, pattern_instructions =
        local_env_of_arg_patterns patterns alpha_sizes
      in
      let body, local_env = compile_expr body alpha_sizes local_env in
      let sizes = local_env |> Local_env.to_list |> List.map ~f:compile_size in
      let foralls = List.map ~f:compile_abstraction foralls in
      let%bind rest_funs, rest_globs = h m in
      return
        ( Instruction.Fun
            ([ name ], (foralls, (args, [ ret ])), sizes, pattern_instructions @ body)
          :: rest_funs
        , rest_globs )
    | LetFun ({ foralls; args; ret; body }, m, _) ->
      let patterns = args in
      let args = args |> List.map ~f:snd |> List.map ~f:compile_type in
      let ret = compile_type ret in
      let alpha_sizes = size_env_of_foralls foralls in
      let local_env, pattern_instructions =
        local_env_of_arg_patterns patterns alpha_sizes
      in
      let body, local_env = compile_expr body alpha_sizes local_env in
      let sizes = local_env |> Local_env.to_list |> List.map ~f:compile_size in
      let foralls = List.map ~f:compile_abstraction foralls in
      let%bind rest_funs, rest_globs = h m in
      return
        ( Instruction.Fun
            ([], (foralls, (args, [ ret ])), sizes, pattern_instructions @ body)
          :: rest_funs
        , rest_globs )
    | Global (e, m, tag) ->
      let alpha_sizes = Size_env.empty in
      let local_env = Local_env.create ~num_arg_locals:0 in
      let (Info { typ; _ }) = e in
      let%bind pretype =
        let pretype, qual = compile_type typ in
        match qual with
        | QualC Unr -> return pretype
        | QualC Lin | QualV _ ->
          Or_error.error_s
            [%message
              "global must be unrestricted"
                ~global:(Source_printer.get_source source_printer tag : string option)]
      in
      let e, local_env = compile_expr e alpha_sizes local_env in
      let%bind () =
        if local_env |> Local_env.to_list |> List.is_empty
        then return ()
        else
          Or_error.error_s
            [%message
              "global required use of locals at codegen time, which is not allowed in \
               richwasm"
                ~global:(Source_printer.get_source source_printer tag : string option)]
      in
      let%bind rest_funs, rest_globs = h m in
      return (rest_funs, Glob.GlobEx ([], pretype, e) :: rest_globs)
    | MainFun { foralls; args; ret; body } ->
      let patterns = args in
      let args = args |> List.map ~f:snd |> List.map ~f:compile_type in
      let ret = compile_type ret in
      let alpha_sizes = size_env_of_foralls foralls in
      let local_env, pattern_instructions =
        local_env_of_arg_patterns patterns alpha_sizes
      in
      let body, local_env = compile_expr body alpha_sizes local_env in
      let sizes = local_env |> Local_env.to_list |> List.map ~f:compile_size in
      let foralls = List.map ~f:compile_abstraction foralls in
      return
        ( [ Instruction.Fun
              ([ "main" ], (foralls, (args, [ ret ])), sizes, pattern_instructions @ body)
          ]
        , [] )
  in
  let%map funs, globs = h m in
  funs, globs, List.init ~f:Fn.id (List.length funs)
;;

let codegen m ~source_printer = codegen m ~source_printer
