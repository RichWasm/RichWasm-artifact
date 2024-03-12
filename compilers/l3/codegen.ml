open! Core
open! Syntax
open! Rich_wasm
open! Typechecked
open Or_error.Let_syntax

module Local_env : sig
  type t [@@deriving sexp]

  val create : num_arg_locals:int -> t
  val bind_arg : int -> t -> t
  val bind : Size.t -> t -> t
  val unbind_exn : t -> t
  val find_exn : int -> t -> int
  val to_list : t -> Size.t list
end = struct
  type t =
    { debruijn_to_local : int list
    ; locals : Size.t list
    ; num_arg_locals : int
    }
  [@@deriving sexp]

  let create ~num_arg_locals =
    { debruijn_to_local = []
    ; locals = List.init num_arg_locals ~f:(fun _ -> Size.SizeC 0)
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

let e_type (Typechecked.Expr.Info { tag = _; typ; e = _ }) = typ

let local_env_of_arg_patterns patterns =
  List.foldi
    patterns
    ~init:(Local_env.create ~num_arg_locals:(List.length patterns))
    ~f:(fun i local_env (pattern, _) ->
      match pattern with
      | `Unit -> local_env
      | `Binding -> Local_env.bind_arg i local_env)
;;

let compile_size i = Size.SizeC (i * 32)
let kind_vars_of_foralls = List.init ~f:(Fn.const KindVar.Loc)

let rec size_of_type (Info (_, t) : Typechecked.Type.t) =
  match t with
  | Int -> 1
  | Unit -> 0
  | Prod ts -> List.sum (module Int) ~f:size_of_type ts
  | Fun _ -> 2
  | Bang t -> size_of_type t
  | Ptr _ | Ref _ -> 2
  | Cap _ -> 0
  | Exists t -> size_of_type t
;;

let compile_type typ =
  let rec h_t (Type.Info (_, typ)) ~is_lin : Rich_wasm.Type.t =
    let h = h_t ~is_lin in
    let qual : Qual.t = if is_lin then QualC Lin else QualC Unr in
    match typ with
    | Int -> Num (Int (S, I32)), qual
    | Unit -> Unit, qual
    | Prod ts -> Prod (List.map ~f:h ts), qual
    | Fun { foralls; args; ret } ->
      let f = h_t ~is_lin:true in
      Coderef (kind_vars_of_foralls foralls, (List.map ~f args, [ f ret ])), qual
    | Bang t -> h_t t ~is_lin:false
    | Ptr v -> Ptr (LocV v), qual
    | Cap (v, t, i) ->
      let t = h_t t ~is_lin:true in
      Cap (W, LocV v, Struct [ t, compile_size i ]), qual
    | Ref (v, t, i, nativity) ->
      (match nativity with
       | Native ->
         let t = h_t t ~is_lin:true in
         Ref (W, LocV v, Struct [ t, compile_size i ]), QualC Lin
       | Foreign ->
         let t = h_t t ~is_lin:false in
         Ref (W, LocV v, Struct [ t, compile_size i ]), QualC Unr)
    | Exists t -> ExLoc (h t), qual
  in
  h_t typ ~is_lin:true
;;

let compile_expr e local_env =
  let rec h_e (Info { tag = _; typ; e } : Typechecked.Expr.t) local_env ~under_bang
    : Rich_wasm.Instruction.t list * Local_env.t * Rich_wasm.LocalEffect.t
    =
    let h = h_e ~under_bang in
    let open Rich_wasm.Instruction in
    match e with
    | Int i ->
      let qualify = if under_bang then [] else [ IQualify (QualC Lin) ] in
      [ IVal (Num (Int (S, I32), Second (Int32.of_int_exn i))) ] @ qualify, local_env, []
    | Binop (e1, e2, op) ->
      let op =
        match op with
        | `Add -> Rich_wasm.IBinOp.Iadd
        | `Sub -> Isub
        | `Mul -> Imul
        | `Div -> Idiv S
      in
      let qualify =
        match typ with
        | Info (_, Bang _) -> []
        | _ -> [ IQualify (QualC Lin) ]
      in
      let e2, local_env, le1 = h e2 local_env in
      let e1, local_env, le2 = h e1 local_env in
      e2 @ e1 @ [ INe (Ib (I32, op)) ] @ qualify, local_env, le1 @ le2
    | Unit ->
      let qualify = if under_bang then [] else [ IQualify (QualC Lin) ] in
      [ IVal Unit ] @ qualify, local_env, []
    | LetUnit { bind; body } ->
      let bind, local_env, le_bind = h bind local_env in
      let body, local_env, le_body = h body local_env in
      bind @ [ IDrop ] @ body, local_env, le_bind @ le_body
    | Prod ts ->
      let (local_env, le), ts =
        List.fold_map ts ~init:(local_env, []) ~f:(fun (local_env, le) t ->
          let t, local_env, le_t = h t local_env in
          (local_env, le @ le_t), t)
      in
      let qual : Qual.t = if under_bang then QualC Unr else QualC Lin in
      List.concat ts @ [ IGroup (List.length ts, qual) ], local_env, le
    | LetProd { vars; bind; body } ->
      let (Info { typ = bind_typ; _ }) = bind in
      let bind, local_env, le_bind = h bind local_env in
      let typs =
        match (bind_typ : Typechecked.Type.t) with
        | Info (_, Prod typs) when List.length typs = List.length vars -> typs
        | _ ->
          raise_s
            [%message
              "BUG: let-prod for prod (with right size) type during code generation"
                (bind_typ : Typechecked.Type.t)
                (List.length vars : int)]
      in
      let local_env, sets, unsets =
        List.fold_left
          (List.zip_exn vars typs)
          ~init:(local_env, [], [])
          ~f:(fun (local_env, sets, unsets) (var, typ) ->
            let size = typ |> size_of_type |> compile_size in
            match var with
            | `Unit -> local_env, [ Instruction.IDrop ] @ sets, unsets
            | `Binding ->
              let local_env = Local_env.bind size local_env in
              let idx = Local_env.find_exn 0 local_env in
              ( local_env
              , [ Instruction.ISet_local idx ] @ sets
              , [ Instruction.IVal Unit; ISet_local idx ] @ unsets ))
      in
      let body, local_env, le_body = h body local_env in
      let local_env =
        List.fold vars ~init:local_env ~f:(fun local_env var ->
          match var with
          | `Unit -> local_env
          | `Binding -> Local_env.unbind_exn local_env)
      in
      bind @ [ IUngroup ] @ sets @ body @ unsets, local_env, le_bind @ le_body
    | Var n ->
      let local = Local_env.find_exn n local_env in
      let qual, le =
        match typ with
        | Info (_, Bang _) -> Qual.QualC Unr, []
        | _ -> Qual.QualC Lin, [ local, ((Unit, QualC Unr) : Rich_wasm.Type.t) ]
      in
      [ IGet_local (local, qual) ], local_env, le
    | Fun n -> [ ICoderefI n ], local_env, []
    | Apply { f; args } ->
      let (local_env, le_args), args =
        List.fold_map args ~init:(local_env, []) ~f:(fun (local_env, le) arg ->
          let arg, local_env, le_arg = h arg local_env in
          (local_env, le @ le_arg), arg)
      in
      let f, local_env, le_f = h f local_env in
      List.concat args @ f @ [ ICall_indirect ], local_env, le_f @ le_args
    | Bang e -> h_e e local_env ~under_bang:true
    | LetBang { var; bind; body } ->
      let (Info { typ = bind_typ; _ }) = bind in
      let size = bind_typ |> size_of_type |> compile_size in
      let bind, local_env, le_bind = h bind local_env in
      let local_env, sets, unsets, qualify_if_not_drop =
        match var with
        | `Unit -> local_env, [ Instruction.IDrop ], [], []
        | `Binding ->
          let local_env = Local_env.bind size local_env in
          let idx = Local_env.find_exn 0 local_env in
          ( local_env
          , [ Instruction.ISet_local idx ]
          , [ Instruction.IVal Unit; ISet_local idx ]
          , [ Instruction.IQualify (QualC Lin) ] )
      in
      let body, local_env, le_body = h body local_env in
      let local_env =
        match var with
        | `Unit -> local_env
        | `Binding -> Local_env.unbind_exn local_env
      in
      bind @ qualify_if_not_drop @ sets @ body @ unsets, local_env, le_bind @ le_body
    | Dupl e ->
      let (Info { typ; _ }) = e in
      let size = typ |> size_of_type |> compile_size in
      let e, local_env, le = h e local_env in
      let local_env = Local_env.bind size local_env in
      let idx = Local_env.find_exn 0 local_env in
      let local_env = Local_env.unbind_exn local_env in
      ( e
        @ [ ISet_local idx
          ; IGet_local (idx, QualC Unr)
          ; IGet_local (idx, QualC Unr)
          ; IVal Unit
          ; ISet_local idx
          ]
      , local_env
      , le )
    | Drop e ->
      let e, local_env, le = h e local_env in
      e @ [ IDrop ], local_env, le
    | New (e, size) ->
      let (Info { typ = e_typ; _ }) = e in
      let e_typ = compile_type e_typ in
      let e, local_env, le = h e local_env in
      let size = compile_size size in
      ( e
        @ [ IStructMalloc ([ size ], QualC Lin)
          ; IMemUnpack
              ( ( []
                , [ ( ExLoc
                        ( Prod
                            [ Cap (W, LocV 0, Struct [ e_typ, size ]), QualC Lin
                            ; Ptr (LocV 0), QualC Unr
                            ]
                        , QualC Lin )
                    , QualC Lin )
                  ] )
              , []
              , [ IRefSplit; IGroup (2, QualC Lin); IMemPack (LocV 0) ] )
          ]
      , local_env
      , le )
    | Free e ->
      let e, local_env, le = h e local_env in
      let rwasm_typ = compile_type typ in
      let size = typ |> size_of_type |> compile_size in
      let local_env = Local_env.bind size local_env in
      let idx = Local_env.find_exn 0 local_env in
      let local_env = Local_env.unbind_exn local_env in
      let qual, undo_local, qualify_mempack =
        match typ with
        | Info (_, Exists (Info (_, Bang _))) ->
          ( Qual.QualC Unr
          , [ Instruction.IVal Unit; ISet_local idx ]
          , [ Instruction.IQualify (QualC Lin) ] )
        | _ -> Qual.QualC Lin, [], []
      in
      ( e
        @ [ IMemUnpack
              ( ([], [ rwasm_typ ])
              , []
              , [ IUngroup
                ; IRefJoin
                ; IVal Unit
                ; IStructSwap 0
                ; ISet_local idx
                ; IStructFree
                ; IGet_local (idx, qual)
                ]
                @ undo_local
                @ [ IMemPack (LocV 0) ]
                @ qualify_mempack )
          ]
      , local_env
      , le )
    | Swap (ptr, cap_and_value) ->
      let (Info { typ = before_pair_typ; _ }) = cap_and_value in
      let before_typ =
        match before_pair_typ with
        | Info (_, Prod [ _; before_typ ]) -> before_typ
        | _ ->
          raise_s
            [%message
              "BUG: the given type to swap was not a pair of a capability and a value"]
      in
      let after_typ =
        match typ with
        | Info (_, Prod [ _; after_typ ]) -> after_typ
        | _ ->
          raise_s
            [%message
              "BUG: the return type of swap was not a pair of a capability and a value"]
      in
      let cap_and_value, local_env, cap_and_value_le = h cap_and_value local_env in
      let ptr, local_env, ptr_le = h ptr local_env in
      let qual_before =
        match before_typ with
        | Info (_, Bang _) -> Qual.QualC Unr
        | _ -> Qual.QualC Lin
      in
      let size_before = before_typ |> size_of_type |> compile_size in
      let local_env = Local_env.bind size_before local_env in
      let idx_before = Local_env.find_exn 0 local_env in
      let local_env = Local_env.unbind_exn local_env in
      let qual_after =
        match after_typ with
        | Info (_, Bang _) -> Qual.QualC Unr
        | _ -> Qual.QualC Lin
      in
      let size_after = after_typ |> size_of_type |> compile_size in
      let local_env = Local_env.bind size_after local_env in
      let idx_after = Local_env.find_exn 0 local_env in
      let local_env = Local_env.unbind_exn local_env in
      ( cap_and_value
        @ [ IUngroup; ISet_local idx_before ]
        @ ptr
        @ [ IRefJoin
          ; IGet_local (idx_before, qual_before)
          ; IVal Unit
          ; ISet_local idx_before
          ; IStructSwap 0
          ; ISet_local idx_after
          ; IRefSplit
          ; IDrop
          ; IGet_local (idx_after, qual_after)
          ; IVal Unit
          ; ISet_local idx_after
          ; IGroup (2, QualC Lin)
          ]
      , local_env
      , cap_and_value_le @ ptr_le )
    | Join e ->
      let typ = compile_type typ in
      let e, local_env, le = h e local_env in
      ( e @ [ IMemUnpack (([], [ typ ]), [], [ IUngroup; IRefJoin; IMemPack (LocV 0) ]) ]
      , local_env
      , le )
    | Split e ->
      let typ = compile_type typ in
      let e, local_env, le = h e local_env in
      ( e
        @ [ IMemUnpack
              (([], [ typ ]), [], [ IRefSplit; IGroup (2, QualC Lin); IMemPack (LocV 0) ])
          ]
      , local_env
      , le )
    | Inst (e, insts) ->
      let e, local_env, le = h e local_env in
      e @ [ IInst (List.map insts ~f:(fun i -> Index.LocI (LocV i))) ], local_env, le
    | Pack (n, e) ->
      let e, local_env, le = h e local_env in
      e @ [ IMemPack (LocV n) ], local_env, le
    | Unpack { var; package; body } ->
      let (Info { typ = package_typ; _ }) = package in
      let (Info { typ = body_type; _ }) = body in
      let body_type = compile_type body_type in
      let size = package_typ |> size_of_type |> compile_size in
      let package, local_env, le_package = h package local_env in
      let local_env, sets, unsets =
        match var with
        | `Unit -> local_env, [ Instruction.IDrop ], []
        | `Binding ->
          let local_env = Local_env.bind size local_env in
          let idx = Local_env.find_exn 0 local_env in
          ( local_env
          , [ Instruction.ISet_local idx ]
          , [ Instruction.IVal Unit; ISet_local idx ] )
      in
      let body, local_env, le_body = h body local_env in
      let local_env =
        match var with
        | `Unit -> local_env
        | `Binding -> Local_env.unbind_exn local_env
      in
      ( package @ [ IMemUnpack (([], [ body_type ]), le_body, sets @ body @ unsets) ]
      , local_env
      , le_package @ le_body )
  in
  let instrs, local_env, _ = h_e e local_env ~under_bang:false in
  instrs, local_env
;;

let codegen (m : Typechecked.Module.t) ~source_printer:_ : Rich_wasm.Module.t Or_error.t =
  let rec h m : Instruction.f list Or_error.t =
    match (m : Module.t) with
    | LetIm ({ typ; mod_name; fun_name }, m) ->
      (match typ with
       | Info (_, Bang (Info (_, Fun { foralls; args; ret }))) ->
         let foralls = kind_vars_of_foralls foralls in
         let args = List.map ~f:compile_type args in
         let ret = compile_type ret in
         let%bind rest_funs = h m in
         return
           (Instruction.FunIm ([], (foralls, (args, [ ret ])), Import (mod_name, fun_name))
            :: rest_funs)
       | _ -> raise_s [%message "BUG: codegen for import of non fun type"])
    | LetEx (name, { foralls; args; body }, m) ->
      let patterns = args in
      let args = args |> List.map ~f:snd |> List.map ~f:compile_type in
      let ret = compile_type (e_type body) in
      let local_env = local_env_of_arg_patterns patterns in
      let body, local_env = compile_expr body local_env in
      let sizes = local_env |> Local_env.to_list in
      let foralls = kind_vars_of_foralls foralls in
      let%bind rest_funs = h m in
      return
        (Instruction.Fun ([ name ], (foralls, (args, [ ret ])), sizes, body) :: rest_funs)
    | Body e ->
      let ret = compile_type (e_type e) in
      let body, local_env = compile_expr e (Local_env.create ~num_arg_locals:0) in
      let sizes = local_env |> Local_env.to_list in
      return [ Instruction.Fun ([], ([], ([], [ ret ])), sizes, body) ]
  in
  let%map funs = h m in
  funs, [], List.init ~f:Fn.id (List.length funs)
;;

let codegen m ~source_printer = codegen m ~source_printer
