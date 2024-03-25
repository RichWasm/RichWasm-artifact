open! Core
open! Rich_wasm
open! Solver
open! Qual
open! Qual_const
open! Or_error.Let_syntax
open! Typing_defs
module Interface = Rich_wasm_compiler_interface
module Ii = Interface.Instruction

let rec strip_unreachable_code es =
  let h = strip_unreachable_code in
  let open Instruction in
  match es with
  | [] -> []
  | IVal v :: rest -> IVal v :: h rest
  | INe n :: rest -> INe n :: h rest
  | IUnreachable :: _ -> [ IUnreachable ]
  | INop :: rest -> INop :: h rest
  | IDrop :: rest -> IDrop :: h rest
  | ISelect :: rest -> ISelect :: h rest
  | IBlock (at, tl, es) :: rest ->
    let es = h es in
    IBlock (at, tl, es) :: h rest
  | ILoop (at, es) :: rest ->
    let es = h es in
    ILoop (at, es) :: h rest
  | IITE (at, tl, es1, es2) :: rest ->
    let es1 = h es1 in
    let es2 = h es2 in
    IITE (at, tl, es1, es2) :: h rest
  | IBr i :: _ -> [ IBr i ]
  | IBr_if i :: rest -> IBr_if i :: h rest
  | IBr_table (is, i) :: _ -> [ IBr_table (is, i) ]
  | IRet :: _ -> [ IRet ]
  | IGet_local (i, q) :: rest -> IGet_local (i, q) :: h rest
  | ISet_local i :: rest -> ISet_local i :: h rest
  | ITee_local i :: rest -> ITee_local i :: h rest
  | IGet_global i :: rest -> IGet_global i :: h rest
  | ISet_global i :: rest -> ISet_global i :: h rest
  | ICoderefI i :: rest -> ICoderefI i :: h rest
  | IInst is :: rest -> IInst is :: h rest
  | ICall_indirect :: rest -> ICall_indirect :: h rest
  | ICall (i, is) :: rest -> ICall (i, is) :: h rest
  | IRecFold pt :: rest -> IRecFold pt :: h rest
  | IRecUnfold :: rest -> IRecUnfold :: h rest
  | IGroup (i, q) :: rest -> IGroup (i, q) :: h rest
  | IUngroup :: rest -> IUngroup :: h rest
  | ICapSplit :: rest -> ICapSplit :: h rest
  | ICapJoin :: rest -> ICapJoin :: h rest
  | IRefDemote :: rest -> IRefDemote :: h rest
  | IMemPack l :: rest -> IMemPack l :: h rest
  | IMemUnpack (at, tl, es) :: rest ->
    let es = h es in
    IMemUnpack (at, tl, es) :: h rest
  | IStructMalloc (szs, q) :: rest -> IStructMalloc (szs, q) :: h rest
  | IStructFree :: rest -> IStructFree :: h rest
  | IStructGet i :: rest -> IStructGet i :: h rest
  | IStructSet i :: rest -> IStructSet i :: h rest
  | IStructSwap i :: rest -> IStructSwap i :: h rest
  | IVariantMalloc (i, ts, q) :: rest -> IVariantMalloc (i, ts, q) :: h rest
  | IVariantCase (q, at, tl, ess) :: rest ->
    let ess = List.map ~f:h ess in
    IVariantCase (q, at, tl, ess) :: h rest
  | IArrayMalloc q :: rest -> IArrayMalloc q :: h rest
  | IArrayGet :: rest -> IArrayGet :: h rest
  | IArraySet :: rest -> IArraySet :: h rest
  | IArrayFree :: rest -> IArrayFree :: h rest
  | IExistPack (pt, ht, q) :: rest -> IExistPack (pt, ht, q) :: h rest
  | IExistUnpack (q, at, tl, es) :: rest ->
    let es = h es in
    IExistUnpack (q, at, tl, es) :: h rest
  | IRefSplit :: rest -> IRefSplit :: h rest
  | IRefJoin :: rest -> IRefJoin :: h rest
  | IQualify q :: rest -> IQualify q :: h rest
;;

module Heapability = struct
  let rec no_caps_type f (pt, _) = no_caps_pretype f pt

  and no_caps_pretype f pt =
    match (pt : Type.pt) with
    | Num _ | Unit | Coderef _ | Ptr _ | Own _ | Ref _ -> return true
    | Var n ->
      Or_error.map (Function_ctx.type_constraints n f) ~f:(function
        | _, _, Heapable -> true
        | _, _, NotHeapable -> false)
    | Prod ts ->
      List.map ts ~f:(no_caps_type f)
      |> Or_error.all
      |> Or_error.map ~f:(List.for_all ~f:Fn.id)
    | Rec (_, t) | ExLoc t -> no_caps_type f t
    | Cap _ -> return false
  ;;
end

module Qual_leq : sig
  val check : Function_ctx.t -> Qual.t -> Qual.t -> bool
end = struct
  let check f qless qgreater =
    let module Solver = (val Function_ctx.qual_solver f) in
    Solver.Qual.check_leq
      ~less:(Solver.Qual.of_qual qless)
      ~greater:(Solver.Qual.of_qual qgreater);
    Solver.check ()
  ;;
end

module Size_leq : sig
  val check : Function_ctx.t -> Size.t -> Size.t -> bool
end = struct
  let check f szless szgreater =
    let module Solver = (val Function_ctx.size_solver f) in
    Solver.Size.check_leq
      ~less:(Solver.Size.of_size szless)
      ~greater:(Solver.Size.of_size szgreater);
    Solver.check ()
  ;;
end

module Validity = struct
  let qual_valid (f : Function_ctx.t) (q : Qual.t) : unit Or_error.t =
    match q with
    | QualC _ -> return ()
    | QualV n ->
      if Function_ctx.qual_bound n f
      then return ()
      else Or_error.error_s [%message "Invalid qualifier" (n : int)]
  ;;

  let rec size_valid (f : Function_ctx.t) (sz : Size.t) : unit Or_error.t =
    match sz with
    | SizeC _ -> return ()
    | SizeV n ->
      if Function_ctx.size_bound n f
      then return ()
      else Or_error.error_s [%message "Invalid size" (n : int)]
    | SizeP (sz1, sz2) ->
      let%bind () = size_valid f sz1 in
      let%bind () = size_valid f sz2 in
      return ()
  ;;

  let loc_valid (f : Function_ctx.t) (LocV n : Loc.t) : unit Or_error.t =
    if Function_ctx.loc_bound n f
    then return ()
    else Or_error.error_s [%message "Invalid loc" (n : int)]
  ;;

  let kind_var_valid f (kv : KindVar.t) =
    match kv with
    | Loc -> return ()
    | Qual (qsl, qsg) -> qsl @ qsg |> List.map ~f:(qual_valid f) |> Or_error.all_unit
    | Size (szsl, szsg) -> szsl @ szsg |> List.map ~f:(size_valid f) |> Or_error.all_unit
    | Type (q, sz, _) ->
      let%bind () = size_valid f sz in
      let%bind () = qual_valid f q in
      return ()
  ;;

  let rec type_valid f ((pt, q) : Type.t) : unit Or_error.t =
    let%bind () = qual_valid f q in
    match pt with
    | Num _ | Unit -> return ()
    | Var n ->
      let%bind q_bound, _, _ = Function_ctx.type_constraints n f in
      if Qual_leq.check f q_bound q
      then return ()
      else
        Or_error.error_s
          [%message
            "Type variable has invalid qualifier"
              (q : Qual.t)
              (q_bound : Qual.t)
              ~type_var:(n : int)]
    | Prod ts ->
      let%bind () = List.map ~f:(type_valid f) ts |> Or_error.all_unit in
      let module Solver = (val Function_ctx.qual_solver f) in
      let open Solver.Qual in
      List.iter ts ~f:(fun (_, q_inner) ->
        check_leq ~less:(of_qual q_inner) ~greater:(of_qual q));
      if Solver.check ()
      then return ()
      else
        Or_error.error_s
          [%message
            "Contents of product were not leq product qualifier"
              ~qual:(q : Qual.t)
              ~types:(ts : Type.t list)]
    | Coderef ft -> fun_type_valid f ft
    | Rec (q_bound, (pt, q_inner)) ->
      let rec rec_var_under_ref var (pt, _) =
        match (pt : Type.pt) with
        | Num _ | Unit | Coderef _ | Ptr _ | Own _ | Ref _ | Cap _ -> Or_error.return ()
        | Var n ->
          if n <> var
          then return ()
          else
            Or_error.error_s
              [%message
                "recursive type does not unfold exclusively into indirections \
                 (infinitely large type)"
                  ~type_:(Rec (q_bound, (pt, q_inner)) : Type.pt)]
        | ExLoc t -> rec_var_under_ref var t
        | Rec (_, t) -> rec_var_under_ref (var + 1) t
        | Prod ts -> List.map ts ~f:(rec_var_under_ref var) |> Or_error.all_unit
      in
      let%bind () = rec_var_under_ref 0 (pt, q_inner) in
      let%bind () = qual_valid f q_bound in
      let%bind sz =
        Sizing.size_of_pretype
          (Function_ctx.size_bounds_of_types f)
          (Rec (q_bound, (pt, q_inner)))
      in
      let%bind f_ext = Function_ctx.add_constraint (Type (q_bound, sz, Heapable)) f in
      let%bind () = type_valid f_ext (pt, q_inner) in
      let module Solver = (val Function_ctx.qual_solver f) in
      let open Solver.Qual in
      check_leq ~less:(of_qual q_inner) ~greater:(of_qual q);
      check_leq ~less:(of_qual q_inner) ~greater:(of_qual q_bound);
      if Solver.check ()
      then return ()
      else
        Or_error.error_s
          [%message
            "Recursive type qualifier inconsistency"
              ~outer_qual:(q : Qual.t)
              ~inner_qual:(q_inner : Qual.t)
              ~qual_bound_on_var:(q_bound : Qual.t)]
    | Ptr l -> loc_valid f l
    | ExLoc (pt, q_inner) ->
      let%bind () =
        if Qual_leq.check f q_inner q
        then return ()
        else
          Or_error.error_s
            [%message
              "Location existential contained greater qualifier"
                ~q_outer:(q : Qual.t)
                (q_inner : Qual.t)]
      in
      let%bind f = Function_ctx.add_constraint Loc f in
      let%bind () = type_valid f (pt, q_inner) in
      return ()
    | Own l ->
      let%bind () = loc_valid f l in
      let%bind () =
        if Qual_leq.check f (QualC Lin) q
        then return ()
        else Or_error.error_s [%message "Own was not linear" (q : Qual.t) (l : Loc.t)]
      in
      return ()
    | Cap (_, l, ht) | Ref (_, l, ht) ->
      let%bind () = loc_valid f l in
      let%bind () = heap_type_valid f ht in
      return ()

  and heap_type_valid (f : Function_ctx.t) (ht : Type.ht) : unit Or_error.t =
    match ht with
    | Variant ts -> ts |> List.map ~f:(type_valid f) |> Or_error.all_unit
    | Struct ts_and_szs ->
      ts_and_szs
      |> List.map ~f:(fun (t, sz) ->
        let%bind () = type_valid f t in
        let%bind () = size_valid f sz in
        let%bind sz_actual =
          Sizing.size_of_type (Function_ctx.size_bounds_of_types f) t
        in
        let%bind () =
          if Size_leq.check f sz_actual sz
          then return ()
          else
            Or_error.error_s
              [%message
                "Type will not fit in annotated size"
                  ~type_:(t : Type.t)
                  ~size:(sz : Size.t)]
        in
        return ())
      |> Or_error.all_unit
    | Array t ->
      let%bind () = type_valid f t in
      let%bind () =
        if Qual_leq.check f (snd t) (QualC Unr)
        then return ()
        else
          Or_error.error_s [%message "Array of non-unrestricted type" ~type_:(t : Type.t)]
      in
      return ()
    | Ex (q_bound, sz, t) ->
      let%bind () = qual_valid f q_bound in
      let%bind () = size_valid f sz in
      let%bind f = Function_ctx.add_constraint (Type (q_bound, sz, Heapable)) f in
      let%bind () = type_valid f t in
      return ()

  and fun_type_valid (f : Function_ctx.t) ((kvs, (ts1, ts2)) : Type.ft) : unit Or_error.t =
    let%bind f =
      List.fold_left kvs ~init:(return f) ~f:(fun f kv ->
        let%bind f = f in
        let%bind () = kind_var_valid f kv in
        Function_ctx.add_constraint kv f)
    in
    ts1 @ ts2 |> List.map ~f:(type_valid f) |> Or_error.all_unit
  ;;
end

module Inst_inds = struct
  let inst_ind f ft i =
    let open KindVar in
    let open Index in
    match ft, i with
    | (Loc :: rest, at), LocI l ->
      let ft = Substitution.Loc.subst_in_ft l (rest, at) in
      return ft
    | (Qual (q_less, q_greater) :: rest, at), QualI q ->
      let%bind () =
        List.fold q_less ~init:(return ()) ~f:(fun acc q_less ->
          let%bind () = acc in
          let%bind () =
            if Qual_leq.check f q_less q
            then return ()
            else
              error_s
                [%message
                  "qualifier being substituted does not meet constraints"
                    ~substituting:(q : Qual.t)
                    ~not_greater_than:(q_less : Qual.t)]
          in
          return ())
      in
      let%bind () =
        List.fold q_greater ~init:(return ()) ~f:(fun acc q_greater ->
          let%bind () = acc in
          let%bind () =
            if Qual_leq.check f q q_greater
            then return ()
            else
              error_s
                [%message
                  "qualifier being substituted does not meet constraints"
                    ~substituting:(q : Qual.t)
                    ~not_less_than:(q_greater : Qual.t)]
          in
          return ())
      in
      let ft = Substitution.Qual.subst_in_ft q (rest, at) in
      return ft
    | (Size (sz_less, sz_greater) :: rest, at), SizeI sz ->
      let%bind () =
        List.fold sz_less ~init:(return ()) ~f:(fun acc sz_less ->
          let%bind () = acc in
          let%bind () =
            if Size_leq.check f sz_less sz
            then return ()
            else
              error_s
                [%message
                  "size being substituted does not meet constraints"
                    ~substituting:(sz : Size.t)
                    ~not_greater_than:(sz_less : Size.t)]
          in
          return ())
      in
      let%bind () =
        List.fold sz_greater ~init:(return ()) ~f:(fun acc sz_greater ->
          let%bind () = acc in
          let%bind () =
            if Size_leq.check f sz sz_greater
            then return ()
            else
              error_s
                [%message
                  "size being substituted does not meet constraints"
                    ~substituting:(sz : Size.t)
                    ~not_less_than:(sz_greater : Size.t)]
          in
          return ())
      in
      let ft = Substitution.Size.subst_in_ft sz (rest, at) in
      return ft
    | (Type (qual, size, heapable) :: rest, at), PretypeI pt ->
      let%bind () =
        let%bind actual_size =
          Sizing.size_of_pretype (Function_ctx.size_bounds_of_types f) pt
        in
        if Size_leq.check f actual_size size
        then return ()
        else
          error_s
            [%message
              "substituting type of too large a size"
                ~type_:(pt : Type.pt)
                ~size:(actual_size : Size.t)
                ~maximum_size:(size : Size.t)]
      in
      let%bind () =
        if Heapable_const.equal heapable Heapable
        then (
          let%bind heapable = Heapability.no_caps_pretype f pt in
          if heapable
          then return ()
          else
            error_s
              [%message
                "attempted to instantiate pretype containing capabilities for a heapable \
                 pretype"
                  ~pretype:(pt : Type.pt)])
        else return ()
      in
      let%bind () = Validity.type_valid f (pt, qual) in
      let ft = Substitution.Type.subst_in_ft pt (rest, at) in
      return ft
    | ft, i ->
      error_s
        [%message
          "Could not instantiate function type with index"
            ~function_type:(ft : Type.ft)
            ~index:(i : Index.t)]
  ;;

  let inst_inds f ft is =
    List.fold is ~init:(return ft) ~f:(fun ft i ->
      let%bind ft = ft in
      inst_ind f ft i)
  ;;
end

module Typecheck_value = struct
  let has_type_value (v : Value.t) =
    match v with
    | Unit -> return (Type.Unit, QualC Unr)
    | Num (t, i) ->
      (match t, i with
       | NumType.Int (s, I32), Second _ ->
         return (Type.Num (NumType.Int (s, I32)), QualC Unr)
       | NumType.Float F32, Second _ -> return (Type.Num (NumType.Float F32), QualC Unr)
       | NumType.Int (s, I64), First _ ->
         return (Type.Num (NumType.Int (s, I64)), QualC Unr)
       | NumType.Float F64, First _ -> return (Type.Num (NumType.Float F64), QualC Unr)
       | _, _ ->
         error_s
           [%message
             "numberical literal does not match type"
               ~numtype:(t : NumType.t)
               ~literal:(i : (int64, int32) Either.t)])
  ;;
end

module Typecheck_instruction : sig
  val typecheck_and_annotate
    :  Instruction.t list
    -> Store_typing.t
    -> Module_type.t
    -> Function_ctx.t
    -> Local_ctx.t
    -> (Ii.t list * (Type.t list * Local_ctx.t) option) Or_error.t
end = struct
  let frame f stack desired_top =
    let rec check_top stack desired =
      match stack, desired with
      | [], [] -> return []
      | framed_out, [] -> return framed_out
      | [], desired ->
        Or_error.error_s [%message "Not enough values on stack" (desired : Type.t list)]
      | top_stack :: stack, top_desired :: desired ->
        if Type.equal top_stack top_desired
        then check_top stack desired
        else
          Or_error.error_s
            [%message
              "Wrong type on stack"
                ~expected:(top_desired : Type.t)
                ~got:(top_stack : Type.t)]
    in
    let%bind framed_out = check_top stack desired_top in
    return
      ( List.fold framed_out ~init:f ~f:(fun f (_, q) ->
          Function_ctx.add_frame_constraint q f)
      , framed_out )
  ;;

  let rec has_type_instruction s c f l es (stack : Type.t list)
    : (Ii.t list * (Type.t list * Local_ctx.t) option) Or_error.t
    =
    match es with
    | [] -> return ([], Some (stack, l))
    | e :: es ->
      (match e with
       | Instruction.IVal v ->
         let%bind tv = Typecheck_value.has_type_value v in
         let%bind es, typ = has_type_instruction s c f l es (tv :: stack) in
         return (Ii.IVal v :: es, typ)
       | INe ne ->
         let%bind stack =
           match ne with
           | Ib (sz1, Iadd) | Ib (sz1, Isub) | Ib (sz1, Imul) ->
             (match stack with
              | (Num (Int (s1, sz2)), _) :: (Num (Int (s2, sz3)), _) :: stack ->
                let%bind () =
                  if Sign.equal s1 s2
                  then return ()
                  else
                    Or_error.error_s
                      [%message
                        "integers of same sign required"
                          ~first:(s1 : Sign.t)
                          ~second:(s2 : Sign.t)]
                in
                let%bind () =
                  if IntType.equal sz1 sz2
                  then return ()
                  else
                    Or_error.error_s
                      [%message
                        "integer on stack did not match annotated size"
                          ~annotated:(sz1 : IntType.t)
                          ~stack:(sz2 : IntType.t)]
                in
                let%bind () =
                  if IntType.equal sz2 sz3
                  then return ()
                  else
                    Or_error.error_s
                      [%message
                        "integers on stack did not match each other"
                          ~first:(sz2 : IntType.t)
                          ~second:(sz3 : IntType.t)]
                in
                return ((Type.Num (Int (s1, sz1)), QualC Unr) :: stack)
              | _ ->
                Or_error.error_s
                  [%message
                    "expected two ints atop the stack"
                      ~instruction:(INe ne : Instruction.t)
                      ~stack:(stack : Type.t list)])
           | Ib (sz1, Idiv s1) ->
             (match stack with
              | (Num (Int (s2, sz2)), _) :: (Num (Int (s3, sz3)), _) :: stack ->
                let%bind () =
                  if Sign.equal s1 s2
                  then return ()
                  else
                    Or_error.error_s
                      [%message
                        "integer on stack did not have annotated sign"
                          ~annotated:(s1 : Sign.t)
                          ~stack:(s2 : Sign.t)]
                in
                let%bind () =
                  if Sign.equal s2 s3
                  then return ()
                  else
                    Or_error.error_s
                      [%message
                        "integers of same sign required"
                          ~first:(s2 : Sign.t)
                          ~second:(s3 : Sign.t)]
                in
                let%bind () =
                  if IntType.equal sz1 sz2
                  then return ()
                  else
                    Or_error.error_s
                      [%message
                        "integer on stack did not match annotated size"
                          ~annotated:(sz1 : IntType.t)
                          ~stack:(sz2 : IntType.t)]
                in
                let%bind () =
                  if IntType.equal sz3 sz2
                  then return ()
                  else
                    Or_error.error_s
                      [%message
                        "integers on stack did not match each other"
                          ~second:(sz3 : IntType.t)
                          ~first:(sz2 : IntType.t)]
                in
                return ((Type.Num (Int (s1, sz1)), QualC Unr) :: stack)
              | _ ->
                Or_error.error_s
                  [%message
                    "expected two ints atop the stack"
                      ~instruction:(INe ne : Instruction.t)
                      ~stack:(stack : Type.t list)])
           | CvtI (sz1, IConvert (sz2, s)) ->
             (match stack with
              | (Num (Int (_, sz)), q) :: stack when IntType.equal sz1 sz ->
                return ((Type.Num (Int (s, sz2)), q) :: stack)
              | _ ->
                Or_error.error_s
                  [%message
                    "top of stack was not an integer of the correct size for conversion"
                      (stack : Type.t list)])
           | _ -> raise_s [%message "Not all numerical instructions are implemented yet"]
         in
         let%bind es, typ = has_type_instruction s c f l es stack in
         return (Ii.INe ne :: es, typ)
       | IUnreachable ->
         if List.is_empty es
         then return ([ Ii.IUnreachable ], None)
         else
           Or_error.error_s
             [%message
               "Unreachable was followed by instructions, so unreachable code must not \
                have been pruned"]
       | INop ->
         let%bind es, typ = has_type_instruction s c f l es stack in
         return (Ii.INop :: es, typ)
       | IDrop ->
         let%bind stack, ptyp =
           match stack with
           | (ptyp, unr) :: rest ->
             if Qual_leq.check f unr (QualC Unr)
             then return (rest, ptyp)
             else
               error_s
                 [%message
                   "Only provably unrestricted values can be dropped with Drop"
                     ~potentially_linear_qualifier:(unr : Qual.t)
                     ~pretype:(ptyp : Type.pt)]
           | [] -> error_s [%message "Drop requires non-empty stack"]
         in
         let%bind es, typ = has_type_instruction s c f l es stack in
         return (Ii.IDrop ptyp :: es, typ)
       | ISelect ->
         let%bind stack =
           match stack with
           | (i32, _) :: (pt_a, q_a) :: (pt_b, q_b) :: rest ->
             let%bind () =
               if Type.equal_pt i32 (Num (Int (U, I32)))
               then return ()
               else
                 error_s
                   [%message
                     "Select requires an unsigned I32 on the top of the stack"
                       ~top_of_stack:(i32 : Type.pt)]
             in
             let%bind () =
               if Type.equal (pt_a, q_a) (pt_b, q_b)
               then return ()
               else
                 error_s
                   [%message
                     "Select requires two values of identical types"
                       ~top_type:((pt_a, q_a) : Type.t)
                       ~bottom_type:((pt_b, q_b) : Type.t)]
             in
             let%bind () =
               if Qual_leq.check f q_a (QualC Unr)
               then return ()
               else
                 error_s
                   [%message
                     "Only provably unrestricted values can be dropped with Select"
                       ~potentially_linear_qualifier:(q_a : Qual.t)]
             in
             return ((pt_a, q_a) :: rest)
           | _ -> error_s [%message "Select requires at least 3 elements on the stack"]
         in
         let%bind es, typ = has_type_instruction s c f l es stack in
         return (Ii.ISelect :: es, typ)
       | IBlock ((input_types, output_types), tl, inner_es) ->
         let%bind l' = Local_ctx.apply_local_effect tl l in
         let%bind stack, inner_annotated =
           let%bind f, framed_out = frame f stack input_types in
           let f = Function_ctx.add_label output_types l' f in
           let%bind inner_annotated, actual_output_and_l'' =
             has_type_instruction s c f l inner_es input_types
           in
           let%bind () =
             match actual_output_and_l'' with
             | None -> return ()
             | Some (actual_output, l'') ->
               let%bind () =
                 if List.equal Type.equal output_types actual_output
                 then return ()
                 else
                   error_s
                     [%message
                       "Block did not return the annotated types"
                         ~expected:(output_types : Type.t list)
                         ~got:(actual_output : Type.t list)]
               in
               let%bind () =
                 if Local_ctx.equal l' l''
                 then return ()
                 else
                   error_s
                     [%message
                       "Block did not have annotated local effect"
                         ~expected:(l' : Local_ctx.t)
                         ~got:(l'' : Local_ctx.t)]
               in
               return ()
           in
           return (output_types @ framed_out, inner_annotated)
         in
         let%bind es, typ = has_type_instruction s c f l' es stack in
         return (Ii.IBlock ((input_types, output_types), tl, inner_annotated) :: es, typ)
       | ILoop ((input_types, output_types), inner_es) ->
         let%bind stack, inner_annotated =
           let%bind f, framed_out = frame f stack input_types in
           let f = Function_ctx.add_label output_types l f in
           let%bind inner_annotated, actual_output_and_l' =
             has_type_instruction s c f l inner_es input_types
           in
           let%bind () =
             match actual_output_and_l' with
             | None -> return ()
             | Some (actual_output, l') ->
               let%bind () =
                 if List.equal Type.equal output_types actual_output
                 then return ()
                 else
                   error_s
                     [%message
                       "Loop did not return the annotated types"
                         ~expected:(output_types : Type.t list)
                         ~got:(actual_output : Type.t list)]
               in
               let%bind () =
                 if Local_ctx.equal l l'
                 then return ()
                 else
                   error_s
                     [%message
                       "Loop had a local effect"
                         ~input_context:(l : Local_ctx.t)
                         ~output_context:(l' : Local_ctx.t)]
               in
               return ()
           in
           return (output_types @ framed_out, inner_annotated)
         in
         let%bind es, typ = has_type_instruction s c f l es stack in
         return (Ii.ILoop ((input_types, output_types), inner_annotated) :: es, typ)
       | IITE ((input_types, output_types), tl, es1, es2) ->
         let%bind l' = Local_ctx.apply_local_effect tl l in
         let%bind stack =
           match stack with
           | (i32, _) :: rest ->
             if Type.equal_pt i32 (Num (Int (U, I32)))
             then return rest
             else
               error_s
                 [%message
                   "ITE requires an unsigned I32 on the top of the stack"
                     ~top_of_stack:(i32 : Type.pt)]
           | [] -> error_s [%message "ITE requires a non-empty stack"]
         in
         let%bind stack, inner_annotated1, inner_annotated2 =
           let%bind f, framed_out = frame f stack input_types in
           let f = Function_ctx.add_label output_types l' f in
           let%bind inner_annotated1, actual_output1_and_l''1 =
             has_type_instruction s c f l es1 input_types
           in
           let%bind inner_annotated2, actual_output2_and_l''2 =
             has_type_instruction s c f l es2 input_types
           in
           let%bind () =
             match actual_output1_and_l''1 with
             | None -> return ()
             | Some (actual_output1, l''1) ->
               let%bind () =
                 if List.equal Type.equal output_types actual_output1
                 then return ()
                 else
                   error_s
                     [%message
                       "Block did not return the annotated types"
                         ~expected:(output_types : Type.t list)
                         ~got:(actual_output1 : Type.t list)]
               in
               let%bind () =
                 if Local_ctx.equal l' l''1
                 then return ()
                 else
                   error_s
                     [%message
                       "Block did not have annotated local effect"
                         ~expected:(l' : Local_ctx.t)
                         ~got:(l''1 : Local_ctx.t)]
               in
               return ()
           in
           let%bind () =
             match actual_output2_and_l''2 with
             | None -> return ()
             | Some (actual_output2, l''2) ->
               let%bind () =
                 if List.equal Type.equal output_types actual_output2
                 then return ()
                 else
                   error_s
                     [%message
                       "Block did not return the annotated types"
                         ~expected:(output_types : Type.t list)
                         ~got:(actual_output2 : Type.t list)]
               in
               let%bind () =
                 if Local_ctx.equal l' l''2
                 then return ()
                 else
                   error_s
                     [%message
                       "Block did not have annotated local effect"
                         ~expected:(l' : Local_ctx.t)
                         ~got:(l''2 : Local_ctx.t)]
               in
               return ()
           in
           return (output_types @ framed_out, inner_annotated1, inner_annotated2)
         in
         let%bind es, typ = has_type_instruction s c f l' es stack in
         return
           ( Ii.IITE ((input_types, output_types), tl, inner_annotated1, inner_annotated2)
             :: es
           , typ )
       | IBr n ->
         let%bind types, local_ctx = Function_ctx.jump_requirements n f in
         let type_count = List.length types in
         let jumping = List.take stack type_count in
         let dropped = List.drop stack type_count in
         let%bind () =
           if List.equal Type.equal types jumping
           then return ()
           else
             error_s
               [%message
                 "breaking with wrong types"
                   ~expected:(types : Type.t list)
                   ~got:(jumping : Type.t list)]
         in
         let%bind () =
           List.fold ~init:(return ()) dropped ~f:(fun acc (ptyp, qual) ->
             let%bind () = acc in
             if Qual_leq.check f qual (QualC Unr)
             then return ()
             else
               error_s
                 [%message
                   "dropping potentially non-linear type" ~type_:((ptyp, qual) : Type.t)])
         in
         let%bind () =
           List.fold ~init:(return ()) (List.range ~stop:`inclusive 0 n) ~f:(fun acc i ->
             let%bind () = acc in
             let%bind quals = Function_ctx.linear_requirements i f in
             if List.for_all quals ~f:(fun qual -> Qual_leq.check f qual (QualC Unr))
             then return ()
             else
               error_s
                 [%message
                   "break would jump over potentially linear values"
                     ~break_number:(n : int)
                     ~linear_ctx_level:(i : int)])
         in
         let%bind () =
           if Local_ctx.equal l local_ctx
           then return ()
           else
             error_s
               [%message
                 "breaking with incorrect local context"
                   ~expected:(local_ctx : Local_ctx.t)
                   ~got:(l : Local_ctx.t)]
         in
         if List.is_empty es
         then return ([ Ii.IBr n ], None)
         else
           Or_error.error_s
             [%message
               "Break was followed by instructions, so unreachable code must not have \
                been pruned"]
       | IBr_if n ->
         let%bind types, local_ctx = Function_ctx.jump_requirements n f in
         let%bind stack =
           match List.hd stack with
           | Some (Num (Int (U, I32)), _) -> return (List.tl_exn stack)
           | Some _ | None ->
             error_s
               [%message "break_if instruction requires an i32 on the top of the stack"]
         in
         let type_count = List.length types in
         let jumping = List.take stack type_count in
         let dropped = List.drop stack type_count in
         let%bind () =
           if List.equal Type.equal types jumping
           then return ()
           else
             error_s
               [%message
                 "breaking with wrong types"
                   ~expected:(types : Type.t list)
                   ~got:(jumping : Type.t list)]
         in
         let%bind () =
           List.fold ~init:(return ()) dropped ~f:(fun acc (ptyp, qual) ->
             let%bind () = acc in
             if Qual_leq.check f qual (QualC Unr)
             then return ()
             else
               error_s
                 [%message
                   "dropping potentially non-linear type" ~type_:((ptyp, qual) : Type.t)])
         in
         let%bind () =
           List.fold ~init:(return ()) (List.range ~stop:`inclusive 0 n) ~f:(fun acc i ->
             let%bind () = acc in
             let%bind quals = Function_ctx.linear_requirements i f in
             if List.for_all quals ~f:(fun qual -> Qual_leq.check f qual (QualC Unr))
             then return ()
             else
               error_s
                 [%message
                   "break_if would jump over potentially linear values"
                     ~break_number:(n : int)
                     ~linear_ctx_level:(i : int)])
         in
         let%bind () =
           if Local_ctx.equal l local_ctx
           then return ()
           else
             error_s
               [%message
                 "breaking with incorrect local context"
                   ~expected:(local_ctx : Local_ctx.t)
                   ~got:(l : Local_ctx.t)]
         in
         let%bind es, typ = has_type_instruction s c f l es stack in
         return (Ii.IBr_if n :: es, typ)
       | IBr_table (is, k) ->
         let typecheck_br f l stack n =
           let%bind types, local_ctx = Function_ctx.jump_requirements n f in
           let type_count = List.length types in
           let jumping = List.take stack type_count in
           let dropped = List.drop stack type_count in
           let%bind () =
             if List.equal Type.equal types jumping
             then return ()
             else
               error_s
                 [%message
                   "breaking with wrong types"
                     ~expected:(types : Type.t list)
                     ~got:(jumping : Type.t list)]
           in
           let%bind () =
             List.fold ~init:(return ()) dropped ~f:(fun acc (ptyp, qual) ->
               let%bind () = acc in
               if Qual_leq.check f qual (QualC Unr)
               then return ()
               else
                 error_s
                   [%message
                     "dropping potentially non-linear type" ~type_:((ptyp, qual) : Type.t)])
           in
           let%bind () =
             List.fold
               ~init:(return ())
               (List.range ~stop:`inclusive 0 n)
               ~f:(fun acc i ->
                 let%bind () = acc in
                 let%bind quals = Function_ctx.linear_requirements i f in
                 if List.for_all quals ~f:(fun qual -> Qual_leq.check f qual (QualC Unr))
                 then return ()
                 else
                   error_s
                     [%message
                       "break_table would jump over potentially linear values"
                         ~break_number:(n : int)
                         ~linear_ctx_level:(i : int)])
           in
           let%bind () =
             if Local_ctx.equal l local_ctx
             then return ()
             else
               error_s
                 [%message
                   "breaking with incorrect local context"
                     ~expected:(local_ctx : Local_ctx.t)
                     ~got:(l : Local_ctx.t)]
           in
           return type_count
         in
         let%bind counts =
           List.map ~f:(typecheck_br f l stack) (k :: is) |> Or_error.all
         in
         let%bind () =
           if List.length counts = 0
              || List.for_all counts ~f:(fun n -> n = List.hd_exn counts)
           then return ()
           else
             error_s
               [%message "All jumps of a break_table must be to labels of the same arity"]
         in
         if List.is_empty es
         then return ([ Ii.IBr_table (is, k) ], None)
         else
           Or_error.error_s
             [%message
               "Break_table was followed by instructions, so unreachable code must not \
                have been pruned"]
       | IRet ->
         (match Function_ctx.ret f with
          | None ->
            error_s
              [%message "return instruction in non-returnable (non-function) context"]
          | Some types ->
            let type_count = List.length types in
            let jumping = List.take stack type_count in
            let dropped = List.drop stack type_count in
            let%bind () =
              if List.equal Type.equal types jumping
              then return ()
              else
                error_s
                  [%message
                    "returning with wrong types"
                      ~expected:(types : Type.t list)
                      ~got:(jumping : Type.t list)]
            in
            let%bind () =
              List.fold ~init:(return ()) dropped ~f:(fun acc (ptyp, qual) ->
                let%bind () = acc in
                if Qual_leq.check f qual (QualC Unr)
                then return ()
                else
                  error_s
                    [%message
                      "dropping potentially non-linear type"
                        ~type_:((ptyp, qual) : Type.t)])
            in
            let%bind () =
              List.fold
                (Function_ctx.all_linear_requirements f)
                ~init:(return ())
                ~f:(fun acc quals ->
                  let%bind () = acc in
                  if List.for_all quals ~f:(fun qual -> Qual_leq.check f qual (QualC Unr))
                  then return ()
                  else
                    error_s [%message "return would jump over potentially linear values"])
            in
            let%bind () =
              List.fold l ~init:(return ()) ~f:(fun acc ((pt, qual), size) ->
                let%bind () = acc in
                if Qual_leq.check f qual (QualC Unr)
                then return ()
                else
                  error_s
                    [%message
                      "returning local_ctx with potentially linear value"
                        ~type_:((pt, qual) : Type.t)
                        ~slot_size:(size : Size.t)])
            in
            if List.is_empty es
            then return ([ Ii.IRet ], None)
            else
              Or_error.error_s
                [%message
                  "Return was followed by instructions, so unreachable code must not \
                   have been pruned"])
       | IGet_local (n, qual_annotation) ->
         let%bind (pt, qual), size =
           match List.nth l n with
           | Some ((pt, qual), size) -> return ((pt, qual), size)
           | None ->
             error_s [%message "Attempt to get non-existant local" ~index:(n : int)]
         in
         let new_slot_type =
           if Qual_leq.check f qual (QualC Unr) then pt, qual else Unit, QualC Unr
         in
         let%bind () = Validity.qual_valid f qual in
         let%bind () =
           if Qual.equal qual qual_annotation
           then return ()
           else
             error_s
               [%message
                 "Qual did not match annotated type on local get"
                   ~expected:(qual_annotation : Qual.t)
                   ~got:(qual : Qual.t)
                   ~slot_number:(n : int)
                   ~slot_type:(pt : Type.pt)]
         in
         let l =
           List.mapi l ~f:(fun i slot -> if i = n then new_slot_type, size else slot)
         in
         let%bind es, typ = has_type_instruction s c f l es ((pt, qual) :: stack) in
         return (Ii.IGet_local (n, qual_annotation, pt) :: es, typ)
       | ISet_local n ->
         let%bind new_type, stack =
           match stack with
           | new_type :: rest -> return (new_type, rest)
           | [] -> error_s [%message "Set local requires non-empty stack"]
         in
         let%bind (_, qual), size =
           match List.nth l n with
           | Some ((pt, qual), size) -> return ((pt, qual), size)
           | None ->
             error_s [%message "Attempt to set non-existant local" ~index:(n : int)]
         in
         let%bind () =
           if Qual_leq.check f qual (QualC Unr)
           then return ()
           else
             error_s
               [%message
                 "Set local would overwrite potentially linear local"
                   ~slot_number:(n : int)
                   ~qualifier:(qual : Qual.t)]
         in
         let%bind new_size =
           Sizing.size_of_type (Function_ctx.size_bounds_of_types f) new_type
         in
         let%bind () =
           if Size_leq.check f new_size size
           then return ()
           else
             error_s
               [%message
                 "Set local with type too large for slot"
                   ~type_:(new_type : Type.t)
                   ~size:(new_size : Size.t)
                   ~slot_size:(size : Size.t)]
         in
         let%bind l = Local_ctx.apply_local_effect [ n, new_type ] l in
         let%bind es, typ = has_type_instruction s c f l es stack in
         return (Ii.ISet_local (n, new_type) :: es, typ)
       | ITee_local n ->
         let%bind new_pt, new_q =
           match stack with
           | new_type :: _ -> return new_type
           | [] -> error_s [%message "Tee local requires non-empty stack"]
         in
         let%bind (_, old_q), size =
           match List.nth l n with
           | Some ((pt, qual), size) -> return ((pt, qual), size)
           | None ->
             error_s [%message "Attempt to tee non-existant local" ~index:(n : int)]
         in
         let%bind () =
           if Qual_leq.check f old_q (QualC Unr)
           then return ()
           else
             error_s
               [%message
                 "Tee local would overwrite potentially linear local"
                   ~slot_number:(n : int)
                   ~qualifier:(old_q : Qual.t)]
         in
         let%bind () =
           if Qual_leq.check f new_q (QualC Unr)
           then return ()
           else
             error_s
               [%message
                 "Tee local would duplicate potentially linear value"
                   ~type_:((new_pt, new_q) : Type.t)]
         in
         let%bind new_size =
           Sizing.size_of_type (Function_ctx.size_bounds_of_types f) (new_pt, new_q)
         in
         let%bind () =
           if Size_leq.check f new_size size
           then return ()
           else
             error_s
               [%message
                 "Tee local with type too large for slot"
                   ~type_:((new_pt, new_q) : Type.t)
                   ~size:(new_size : Size.t)
                   ~slot_size:(size : Size.t)]
         in
         let%bind l = Local_ctx.apply_local_effect [ n, (new_pt, new_q) ] l in
         let%bind es, typ = has_type_instruction s c f l es stack in
         return (Ii.ITee_local (n, (new_pt, new_q)) :: es, typ)
       | IGet_global n ->
         let%bind pt =
           match List.nth c.Module_type.globs n with
           | Some (_, pt) -> return pt
           | None ->
             error_s [%message "Attempt to get non-existant global" ~index:(n : int)]
         in
         let%bind es, typ = has_type_instruction s c f l es ((pt, QualC Unr) :: stack) in
         return (Ii.IGet_global n :: es, typ)
       | ISet_global n ->
         let%bind glob_mut, glob_pt =
           match List.nth c.Module_type.globs n with
           | Some pt -> return pt
           | None ->
             error_s [%message "Attempt to get non-existant global" ~index:(n : int)]
         in
         let%bind stack_pt, stack =
           match stack with
           | (pt, unr) :: rest ->
             if Qual_leq.check f unr (QualC Unr)
             then return (pt, rest)
             else
               error_s
                 [%message
                   "Only provably unrestricted values can be set to globals"
                     ~potentially_linear_qualifier:(unr : Qual.t)
                     ~index:(n : int)]
           | [] -> error_s [%message "Set global requires non-empty stack"]
         in
         let%bind () =
           if [%equal: Type.pt] glob_pt stack_pt && glob_mut
           then return ()
           else
             error_s
               [%message
                 "Wrong type for set global"
                   ~expected:(glob_pt : Type.pt)
                   ~got:(stack_pt : Type.pt)]
         in
         let%bind es, typ = has_type_instruction s c f l es stack in
         return (Ii.ISet_global n :: es, typ)
       | ICoderefI n ->
         let%bind ft =
           match List.nth c.Module_type.table n with
           | Some ft -> return ft
           | None ->
             error_s [%message "Coderef index not found in table" ~index:(n : int)]
         in
         let type_ = Type.Coderef ft, QualC Unr in
         let%bind () = Validity.type_valid f type_ in
         let%bind es, typ = has_type_instruction s c f l es (type_ :: stack) in
         return (Ii.ICoderefI n :: es, typ)
       | IInst is ->
         let%bind ft, q, stack =
           match List.hd stack with
           | Some (Coderef ft, q) -> return (ft, q, List.tl_exn stack)
           | Some type_ ->
             error_s [%message "Inst requires coderef on stack" ~got:(type_ : Type.t)]
           | None -> error_s [%message "Inst requires non-empty stack"]
         in
         let%bind ft = Inst_inds.inst_inds f ft is in
         let%bind es, typ = has_type_instruction s c f l es ((Coderef ft, q) :: stack) in
         return (Ii.IInst is :: es, typ)
       | ICall_indirect ->
         let%bind taus_in, taus_out, stack =
           match List.hd stack with
           | Some (Coderef ([], (taus_in, taus_out)), _) ->
             return (taus_in, taus_out, List.tl_exn stack)
           | Some type_ ->
             error_s
               [%message
                 "Call indirect requires fully instantiated coderef on stack"
                   ~got:(type_ : Type.t)]
           | None -> error_s [%message "Call indirect requires non-empty stack"]
         in
         let type_count = List.length taus_in in
         let call_with = List.take stack type_count |> List.rev in
         let framed_out = List.drop stack type_count in
         let%bind () =
           if List.equal Type.equal taus_in call_with
           then return ()
           else
             error_s
               [%message
                 "calling coderef with wrong types"
                   ~expected:(taus_in : Type.t list)
                   ~got:(call_with : Type.t list)]
         in
         let%bind es, typ =
           has_type_instruction s c f l es (List.rev taus_out @ framed_out)
         in
         return (Ii.ICall_indirect (taus_in, taus_out) :: es, typ)
       | ICall (n, is) ->
         let%bind ft =
           match List.nth c.Module_type.funcs n with
           | Some ft -> return ft
           | None -> error_s [%message "Calling invalid function index" ~index:(n : int)]
         in
         let%bind ft = Inst_inds.inst_inds f ft is in
         let%bind taus_in, taus_out =
           match ft with
           | [], (taus_in, taus_out) -> return (taus_in, taus_out)
           | ft ->
             error_s
               [%message
                 "Call must fully instantiate function types"
                   ~instantiated_type:(ft : Type.ft)]
         in
         let type_count = List.length taus_in in
         let call_with = List.take stack type_count |> List.rev in
         let framed_out = List.drop stack type_count in
         let%bind () =
           if List.equal Type.equal taus_in call_with
           then return ()
           else
             error_s
               [%message
                 "calling function with wrong types"
                   ~expected:(taus_in : Type.t list)
                   ~got:(call_with : Type.t list)]
         in
         let%bind es, typ =
           has_type_instruction s c f l es (List.rev taus_out @ framed_out)
         in
         return (Ii.ICall (n, is) :: es, typ)
       | IRecFold pt ->
         let%bind t =
           match pt with
           | Rec (_, t) -> return t
           | _ ->
             Or_error.error_s
               [%message
                 "rec.fold must be annotated with a recursive type"
                   ~annotation:(pt : Type.pt)]
         in
         let%bind stack, (unfolded_on_stack, q) =
           match stack with
           | [] -> Or_error.error_s [%message "exist.pack requires non-empty stack"]
           | t :: stack -> return (stack, t)
         in
         let unfolded_type = Substitution.Type.subst_in_t pt t in
         let%bind () =
           if Type.equal (unfolded_on_stack, q) unfolded_type
           then return ()
           else
             Or_error.error_s
               [%message
                 "unfolded annotation was not equal to top of stack for rec.fold"
                   ~top_of_stack:((unfolded_on_stack, q) : Type.t)
                   ~unfolded_annotation:(unfolded_type : Type.t)]
         in
         let%bind () = Validity.type_valid f (pt, q) in
         let%bind () = Validity.type_valid f unfolded_type in
         let%bind es, typ = has_type_instruction s c f l es ((pt, q) :: stack) in
         return (Ii.IRecFold pt :: es, typ)
       | IRecUnfold ->
         let%bind stack, (rec_pretype, q) =
           match stack with
           | [] -> Or_error.error_s [%message "exist.pack requires non-empty stack"]
           | t :: stack -> return (stack, t)
         in
         let%bind t =
           match rec_pretype with
           | Rec (_, t) -> return t
           | _ ->
             Or_error.error_s
               [%message
                 "rec.unfold requires a recursive type on top of the stack"
                   ~top_of_stack:(rec_pretype : Type.pt)]
         in
         let unfolded_type = Substitution.Type.subst_in_t rec_pretype t in
         let%bind () = Validity.type_valid f (rec_pretype, q) in
         let%bind () = Validity.type_valid f unfolded_type in
         let%bind es, typ = has_type_instruction s c f l es (unfolded_type :: stack) in
         return (Ii.IRecUnfold :: es, typ)
       | IGroup (n, q) ->
         let grouping = List.take stack n |> List.rev in
         let framed_out = List.drop stack n in
         let%bind () =
           List.fold ~init:(return ()) framed_out ~f:(fun acc (pt, qual) ->
             let%bind () = acc in
             if Qual_leq.check f qual q
             then return ()
             else
               error_s
                 [%message
                   "putting type into group of potentially lower qualifier"
                     ~group_qual:(q : Qual.t)
                     ~type_:((pt, qual) : Type.t)])
         in
         let%bind es, typ =
           has_type_instruction s c f l es ((Prod grouping, q) :: framed_out)
         in
         return (Ii.IGroup (n, q) :: es, typ)
       | IUngroup ->
         let%bind taus, stack =
           match List.hd stack with
           | Some (Prod ts, _) -> return (List.rev ts, List.tl_exn stack)
           | Some type_ ->
             error_s [%message "Ungroup requires a product type" ~got:(type_ : Type.t)]
           | None -> error_s [%message "Ungroup requires a non-empty stack"]
         in
         let%bind es, typ = has_type_instruction s c f l es (taus @ stack) in
         return (Ii.IUngroup :: es, typ)
       | ICapSplit ->
         let%bind loc, ht, stack =
           match List.hd stack with
           | Some (Cap (W, loc, ht), QualC Lin) -> return (loc, ht, List.tl_exn stack)
           | Some type_ ->
             error_s
               [%message
                 "Cap split requires a linear write capability" ~got:(type_ : Type.t)]
           | None -> error_s [%message "Cap split requires a non-empty stack"]
         in
         let%bind es, typ =
           has_type_instruction
             s
             c
             f
             l
             es
             ((Cap (R, loc, ht), QualC Lin) :: (Own loc, QualC Lin) :: stack)
         in
         return (Ii.ICapSplit :: es, typ)
       | ICapJoin ->
         let open Loc in
         let%bind loc, ht, stack =
           match List.take stack 2 with
           | [ (Cap (R, LocV n1, ht), QualC Lin); (Own (LocV n2), QualC Lin) ]
             when n1 = n2 -> return (LocV n1, ht, List.drop stack 2)
           | _ ->
             error_s
               [%message
                 "Cap join requires a matching linear read capability and linear \
                  ownership token on top of the stack"
                   ~got:(stack : Type.t list)]
         in
         let%bind es, typ =
           has_type_instruction s c f l es ((Cap (W, loc, ht), QualC Lin) :: stack)
         in
         return (Ii.ICapJoin :: es, typ)
       | IRefDemote ->
         let%bind loc, ht, stack =
           match List.hd stack with
           | Some (Ref (W, loc, ht), QualC Unr) -> return (loc, ht, List.tl_exn stack)
           | Some type_ ->
             error_s
               [%message
                 "Ref demote requires an unrestricted write reference"
                   ~got:(type_ : Type.t)]
           | None -> error_s [%message "Ref demote requires a non-empty stack"]
         in
         let%bind es, typ =
           has_type_instruction s c f l es ((Ref (R, loc, ht), QualC Unr) :: stack)
         in
         return (Ii.IRefDemote :: es, typ)
       | IMemPack location ->
         let local_ctx = l in
         let l = location in
         let%bind () = Validity.loc_valid f l in
         let%bind stack, typ_to_pack =
           match stack with
           | [] -> Or_error.error_s [%message "mempack requires non-empty stack"]
           | t :: stack -> return (stack, t)
         in
         let%bind () = Validity.type_valid f typ_to_pack in
         let shift_l (Loc.LocV n) shift = Loc.LocV (n + shift) in
         let rec abstract_loc_in_typ l depth (pt, q) =
           let replace_loc l' = if Loc.equal l l' then Loc.LocV depth else l' in
           match (pt : Type.pt) with
           | Num _ | Var _ | Unit -> pt, q
           | Prod ts -> Type.Prod (List.map ~f:(abstract_loc_in_typ l depth) ts), q
           | Coderef ft -> Coderef (abstract_loc_in_ft l depth ft), q
           | Rec (q, t) -> Rec (q, abstract_loc_in_typ l depth t), q
           | Ptr l' -> Ptr (replace_loc l'), q
           | ExLoc t -> ExLoc (abstract_loc_in_typ (shift_l l 1) (depth + 1) t), q
           | Own l' -> Own (replace_loc l'), q
           | Cap (cap, l', ht) ->
             Cap (cap, replace_loc l', abstract_loc_in_ht l depth ht), q
           | Ref (cap, l', ht) ->
             Ref (cap, replace_loc l', abstract_loc_in_ht l depth ht), q
         and abstract_loc_in_ht l depth = function
           | Variant ts -> Variant (List.map ~f:(abstract_loc_in_typ l depth) ts)
           | Struct ts_szs ->
             Struct
               (List.map ts_szs ~f:(fun (t, sz) -> abstract_loc_in_typ l depth t, sz))
           | Array t -> Array (abstract_loc_in_typ l depth t)
           | Ex (q, sz, t) -> Ex (q, sz, abstract_loc_in_typ l depth t)
         and abstract_loc_in_at l depth (ts1, ts2) =
           let f = abstract_loc_in_typ l depth in
           List.map ~f ts1, List.map ~f ts2
         and abstract_loc_in_ft l depth (kvs, at) =
           let depth_increase =
             List.count kvs ~f:(fun kv ->
               match (kv : KindVar.t) with
               | Loc -> true
               | _ -> false)
           in
           kvs, abstract_loc_in_at (shift_l l depth_increase) (depth + depth_increase) at
         in
         let typ_to_pack = Substitution.Loc.incr_unbound_in_t 1 typ_to_pack in
         let l = shift_l l 1 in
         let package_pt, package_q = abstract_loc_in_typ l 0 typ_to_pack in
         let%bind es, typ =
           has_type_instruction
             s
             c
             f
             local_ctx
             es
             ((ExLoc (package_pt, package_q), package_q) :: stack)
         in
         return (Ii.IMemPack l :: es, typ)
       | IMemUnpack ((input_types, output_types), tl, inner_es) ->
         let input_types = List.rev input_types in
         let output_types = List.rev output_types in
         let shift_types = List.map ~f:(Substitution.Loc.incr_unbound_in_t 1) in
         let shift_locals =
           List.map ~f:(fun (t, sz) -> Substitution.Loc.incr_unbound_in_t 1 t, sz)
         in
         let%bind l' = Local_ctx.apply_local_effect tl l in
         let%bind stack, t_rho =
           match stack with
           | [] -> Or_error.error_s [%message "mem.unpack requires non-empty stack"]
           | t :: stack ->
             (match t with
              | ExLoc t_rho, _ -> return (stack, t_rho)
              | _ ->
                Or_error.error_s
                  [%message
                    "mem.unpack requires an ExLoc on the top of the stack"
                      ~actual_top:(t : Type.t)])
         in
         let%bind () =
           input_types |> List.map ~f:(Validity.type_valid f) |> Or_error.all_unit
         in
         let%bind () =
           output_types |> List.map ~f:(Validity.type_valid f) |> Or_error.all_unit
         in
         let%bind stack, inner_annotated =
           let%bind f, framed_out = frame f stack input_types in
           let f = Function_ctx.add_label output_types l' f in
           let%bind f = Function_ctx.add_constraint Loc f in
           let l = shift_locals l in
           let input_types = shift_types input_types in
           let%bind inner_annotated, actual_output_and_l'' =
             has_type_instruction s c f l inner_es (t_rho :: input_types)
           in
           let%bind () =
             match actual_output_and_l'' with
             | None -> return ()
             | Some (actual_output, l'') ->
               let%bind () =
                 let output_types = shift_types output_types in
                 if List.equal Type.equal output_types actual_output
                 then return ()
                 else
                   error_s
                     [%message
                       "mem.unpack did not return the annotated types"
                         ~expected:(output_types : Type.t list)
                         ~got:(actual_output : Type.t list)]
               in
               let%bind () =
                 let l' = shift_locals l' in
                 if Local_ctx.equal l' l''
                 then return ()
                 else
                   error_s
                     [%message
                       "mem.unpack did not have annotated local effect"
                         ~expected:(l' : Local_ctx.t)
                         ~got:(l'' : Local_ctx.t)]
               in
               return ()
           in
           return (output_types @ framed_out, inner_annotated)
         in
         let%bind es, typ = has_type_instruction s c f l' es stack in
         return
           (Ii.IMemUnpack ((List.rev input_types, List.rev output_types), tl, inner_annotated, t_rho) :: es, typ)
       | IStructMalloc (szs, q) ->
         let%bind taus_szs, stack =
           let length = List.length szs in
           let taus = List.take stack length in
           let stack = List.drop stack length in
           match List.zip (List.rev taus) szs with
           | Ok taus_szs -> return (taus_szs, stack)
           | Unequal_lengths ->
             Or_error.error_s
               [%message
                 "too few values on stack for struct.malloc"
                   ~stack:(stack : Type.t list)
                   ~number_needed:(length : int)]
         in
         let%bind () = Validity.qual_valid f q in
         let%bind taus_szs, taus_for_annotation =
           taus_szs
           |> List.map ~f:(fun (tau, sz) ->
             let%bind () = Validity.type_valid f tau in
             let%bind () = Validity.size_valid f sz in
             let%bind size_of_type =
               Sizing.size_of_type (Function_ctx.size_bounds_of_types f) tau
             in
             let%bind () =
               if Size_leq.check f size_of_type sz
               then return ()
               else
                 Or_error.error_s
                   [%message
                     "type will not fit in size for struct.malloc"
                       ~type_:(tau : Type.t)
                       ~size:(sz : Size.t)]
             in
             let%bind b = Heapability.no_caps_type f tau in
             if b || Qual_leq.check f (QualC Lin) q
             then return ((Substitution.Loc.incr_unbound_in_t 1 tau, sz), tau)
             else
               Or_error.error_s
                 [%message
                   "struct.malloc called with type containing caps" ~type_:(tau : Type.t)])
           |> Or_error.all
           |> Or_error.map ~f:List.unzip
         in
         let return_type : Type.t = ExLoc (Ref (W, LocV 0, Struct taus_szs), q), q in
         let%bind es, typ = has_type_instruction s c f l es (return_type :: stack) in
         return (Ii.IStructMalloc (szs, q, taus_for_annotation) :: es, typ)
       | IStructFree ->
         let%bind stack, taus_szs, q_ref =
           match stack with
           | (Ref (W, _, Struct taus_szs), q_ref) :: stack ->
             return (stack, taus_szs, q_ref)
           | _ ->
             Or_error.error_s
               [%message
                 "struct.free requires a stack with a writable reference to a struct on \
                  the top of the stack"
                   ~actual_stack:(stack : Type.t list)]
         in
         let%bind () =
           if Qual_leq.check f (QualC Lin) q_ref
           then return ()
           else
             Or_error.error_s
               [%message
                 "attempted to free a potentially non-linear struct"
                   ~qualifier:(q_ref : Qual.t)]
         in
         let%bind type_annotations =
           taus_szs
           |> List.map ~f:(fun (tau, _) ->
             if Qual_leq.check f (snd tau) (QualC Unr)
             then return tau
             else
               Or_error.error_s
                 [%message
                   "attempting to free struct with linear contents" ~type_:(tau : Type.t)])
           |> Or_error.all
         in
         let%bind es, typ = has_type_instruction s c f l es stack in
         return (Ii.IStructFree type_annotations :: es, typ)
       | IStructGet n ->
         let%bind stack, taus_szs =
           match stack with
           | (Ref (_, _, Struct taus_szs), _) :: _ -> return (stack, taus_szs)
           | _ ->
             Or_error.error_s
               [%message
                 "struct.get requires a stack with a reference to a struct on the top of \
                  the stack"
                   ~actual_stack:(stack : Type.t list)]
         in
         let%bind typ =
           match List.nth taus_szs n with
           | Some (typ, _) -> return typ
           | None ->
             Or_error.error_s
               [%message
                 "struct.get had too high an index"
                   ~index:(n : int)
                   ~number_of_types:(List.length taus_szs : int)]
         in
         let type_annotations = List.map ~f:fst taus_szs in
         let%bind () =
           if Qual_leq.check f (snd typ) (QualC Unr)
           then return ()
           else
             Or_error.error_s
               [%message
                 "struct.get attempted to duplicate a non-linear value"
                   ~qualifier:(snd typ : Qual.t)]
         in
         let%bind es, typ = has_type_instruction s c f l es (typ :: stack) in
         return (Ii.IStructGet (n, type_annotations) :: es, typ)
       | IStructSet n ->
         let%bind stack, typ, loc, taus_szs, q_ref =
           match stack with
           | typ :: (Ref (W, loc, Struct taus_szs), q_ref) :: stack ->
             return (stack, typ, loc, taus_szs, q_ref)
           | _ ->
             Or_error.error_s
               [%message
                 "struct.set requires a stack with a value and a writable reference to a \
                  struct on the top of the stack"
                   ~actual_stack:(stack : Type.t list)]
         in
         let pretype_to_annotate, _ = typ in
         let%bind old_typ, sz =
           match List.nth taus_szs n with
           | Some typ_sz -> return typ_sz
           | None ->
             Or_error.error_s
               [%message
                 "struct.set had too high an index"
                   ~index:(n : int)
                   ~number_of_types:(List.length taus_szs : int)]
         in
         let%bind () =
           if Qual_leq.check f (snd old_typ) (QualC Unr)
           then return ()
           else
             Or_error.error_s
               [%message
                 "struct.set attempted to drop a potentially linear value"
                   ~qualifier:(snd old_typ : Qual.t)]
         in
         let%bind size_of_typ =
           Sizing.size_of_type (Function_ctx.size_bounds_of_types f) typ
         in
         let%bind () =
           if Size_leq.check f size_of_typ sz
           then return ()
           else
             Or_error.error_s
               [%message
                 "struct.set was called with type which wouldn't fit in slot"
                   ~type_:(typ : Type.t)
                   ~size:(sz : Size.t)]
         in
         let%bind () =
           let%bind b = Heapability.no_caps_type f typ in
           if b || Qual_leq.check f (QualC Lin) q_ref
           then return ()
           else
             Or_error.error_s
               [%message
                 "struct.set called with type containing caps" ~type_:(typ : Type.t)]
         in
         let%bind () =
           if Qual_leq.check f (QualC Lin) q_ref || Type.equal typ old_typ
           then return ()
           else
             Or_error.error_s
               [%message
                 "struct.set attempted a strong update on a non-linear struct"
                   ~old_type:(old_typ : Type.t)
                   ~new_type:(typ : Type.t)
                   ~index:(n : int)]
         in
         let taus_szs' =
           List.mapi taus_szs ~f:(fun i (cur_typ, sz) ->
             if i = n then typ, sz else cur_typ, sz)
         in
         let%bind es, typ =
           has_type_instruction
             s
             c
             f
             l
             es
             ((Ref (W, loc, Struct taus_szs'), q_ref) :: stack)
         in
         let type_annotations = List.map ~f:fst taus_szs in
         return (Ii.IStructSet (n, type_annotations, pretype_to_annotate) :: es, typ)
       | IStructSwap n ->
         let%bind stack, typ, loc, taus_szs, q_ref =
           match stack with
           | typ :: (Ref (W, loc, Struct taus_szs), q_ref) :: stack ->
             return (stack, typ, loc, taus_szs, q_ref)
           | _ ->
             Or_error.error_s
               [%message
                 "struct.swap requires a stack with a value and a writable reference to \
                  a struct on the top of the stack"
                   ~actual_stack:(stack : Type.t list)]
         in
         let pretype_to_annotate, _ = typ in
         let%bind old_typ, sz =
           match List.nth taus_szs n with
           | Some typ_sz -> return typ_sz
           | None ->
             Or_error.error_s
               [%message
                 "struct.swap had too high an index"
                   ~index:(n : int)
                   ~number_of_types:(List.length taus_szs : int)]
         in
         let%bind size_of_typ =
           Sizing.size_of_type (Function_ctx.size_bounds_of_types f) typ
         in
         let%bind () =
           if Size_leq.check f size_of_typ sz
           then return ()
           else
             Or_error.error_s
               [%message
                 "struct.swap was called with type which wouldn't fit in slot"
                   ~type_:(typ : Type.t)
                   ~size:(sz : Size.t)]
         in
         let%bind () =
           let%bind b = Heapability.no_caps_type f typ in
           if b || Qual_leq.check f (QualC Lin) q_ref
           then return ()
           else
             Or_error.error_s
               [%message
                 "struct.swap called with type containing caps" ~type_:(typ : Type.t)]
         in
         let%bind () =
           if Qual_leq.check f (QualC Lin) q_ref || Type.equal typ old_typ
           then return ()
           else
             Or_error.error_s
               [%message
                 "struct.swap attempted a strong update on a non-linear struct"
                   ~old_type:(old_typ : Type.t)
                   ~new_type:(typ : Type.t)
                   ~index:(n : int)]
         in
         let taus_szs' =
           List.mapi taus_szs ~f:(fun i (cur_typ, sz) ->
             if i = n then typ, sz else cur_typ, sz)
         in
         let%bind es, typ =
           has_type_instruction
             s
             c
             f
             l
             es
             (old_typ :: (Ref (W, loc, Struct taus_szs'), q_ref) :: stack)
         in
         let type_annotations = List.map ~f:fst taus_szs in
         return (Ii.IStructSwap (n, type_annotations, pretype_to_annotate) :: es, typ)
       | IVariantMalloc (n, ts, q) ->
         let%bind t =
           match List.nth ts n with
           | Some t -> return t
           | None ->
             Or_error.error_s
               [%message
                 "variant.malloc had too high an index"
                   ~index:(n : int)
                   ~number_of_types:(List.length ts : int)]
         in
         let%bind ts_heap =
           ts
           |> List.map ~f:(fun t ->
             let%bind () = Validity.type_valid f t in
             let%bind b = Heapability.no_caps_type f t in
             if b || Qual_leq.check f (QualC Lin) q
             then return (Substitution.Loc.incr_unbound_in_t 1 t)
             else
               Or_error.error_s
                 [%message
                   "variant.malloc attempted to put caps on the heap" ~type_:(t : Type.t)])
           |> Or_error.all
         in
         let%bind () = Validity.qual_valid f q in
         let%bind () =
           if Qual_leq.check f (snd t) q
           then return ()
           else
             Or_error.error_s
               [%message
                 "variant.malloc attempted to put a value into a potentially more linear \
                  reference"
                   ~type_:(t : Type.t)
                   ~qual:(q : Qual.t)]
         in
         let%bind stack, typ =
           match stack with
           | typ :: stack -> return (stack, typ)
           | [] ->
             Or_error.error_s
               [%message
                 "variant.malloc requires a non_empty stack"
                   ~actual_stack:(stack : Type.t list)]
         in
         let%bind () =
           if Type.equal t typ
           then return ()
           else
             Or_error.error_s
               [%message
                 "variant.malloc given wrong type"
                   ~annotated:(t : Type.t)
                   ~stack:(typ : Type.t)]
         in
         let return_type : Type.t = ExLoc (Ref (W, LocV 0, Variant ts_heap), q), q in
         let%bind es, typ = has_type_instruction s c f l es (return_type :: stack) in
         return (Ii.IVariantMalloc (n, ts, q) :: es, typ)
       | IVariantCase (q_mem_type, (input_types, output_types), tl, inner_ess) ->
         let%bind () = Validity.qual_valid f q_mem_type in
         (match
            ( Qual_leq.check f q_mem_type (QualC Unr)
            , Qual_leq.check f (QualC Lin) q_mem_type )
          with
          | false, false ->
            Or_error.error_s
              [%message
                "variant.case qual annotation could not be determined to be linear or \
                 unrestricted"]
          | true, true ->
            raise_s
              [%message
                "BUG: qualifier was determined to be both linear and unrestricted"]
          | true, false ->
            let%bind l' = Local_ctx.apply_local_effect tl l in
            let%bind stack, ts, qv, ref_typ_to_return =
              match stack with
              | [] -> Or_error.error_s [%message "variant.case requires non-empty stack"]
              | t :: stack ->
                (match t with
                 | Ref (_, _, Variant ts), qv -> return (stack, ts, qv, t)
                 | _ ->
                   Or_error.error_s
                     [%message
                       "variant.case requires a reference to a variant on the top of the \
                        stack"
                         ~actual_top:(t : Type.t)])
            in
            let%bind () =
              input_types |> List.map ~f:(Validity.type_valid f) |> Or_error.all_unit
            in
            let%bind () =
              output_types |> List.map ~f:(Validity.type_valid f) |> Or_error.all_unit
            in
            let%bind () =
              List.map ts ~f:(fun t ->
                if Qual_leq.check f (snd t) (QualC Unr)
                then return ()
                else
                  Or_error.error_s
                    [%message
                      "Contents of variant for variant.case must be unrestricted if the \
                       annotation is unrestricted"
                        ~actual:(snd t : Qual.t)])
              |> Or_error.all_unit
            in
            let%bind inner_ess_and_ts =
              match List.zip inner_ess ts with
              | Ok l -> return l
              | Unequal_lengths ->
                Or_error.error_s
                  [%message
                    "variant.case had wrong number of cases"
                      ~num_cases:(List.length inner_ess : int)
                      ~types:(ts : Type.t list)]
            in
            let%bind stack, inner_annotated =
              let%bind f, framed_out = frame f stack input_types in
              let f = Function_ctx.add_frame_constraint qv f in
              let f = Function_ctx.add_label output_types l' f in
              let%bind inner_annotated =
                List.map inner_ess_and_ts ~f:(fun (inner_es, inner_t) ->
                  let%bind inner_annotated, actual_output_and_l'' =
                    has_type_instruction s c f l inner_es (inner_t :: input_types)
                  in
                  let%bind () =
                    match actual_output_and_l'' with
                    | None -> return ()
                    | Some (actual_output, l'') ->
                      let%bind () =
                        if List.equal Type.equal output_types actual_output
                        then return ()
                        else
                          error_s
                            [%message
                              "variant.case did not return the annotated types"
                                ~expected:(output_types : Type.t list)
                                ~got:(actual_output : Type.t list)]
                      in
                      let%bind () =
                        if Local_ctx.equal l' l''
                        then return ()
                        else
                          error_s
                            [%message
                              "variant.case did not have annotated local effect"
                                ~expected:(l' : Local_ctx.t)
                                ~got:(l'' : Local_ctx.t)]
                      in
                      return ()
                  in
                  return inner_annotated)
                |> Or_error.all
              in
              return (output_types @ [ ref_typ_to_return ] @ framed_out, inner_annotated)
            in
            let%bind es, typ = has_type_instruction s c f l' es stack in
            return
              ( Ii.IVariantCase
                  (q_mem_type, ts, (input_types, output_types), tl, inner_annotated)
                :: es
              , typ )
          | false, true ->
            let%bind l' = Local_ctx.apply_local_effect tl l in
            let%bind stack, ts, qv =
              match stack with
              | [] -> Or_error.error_s [%message "variant.case requires non-empty stack"]
              | t :: stack ->
                (match t with
                 | Ref (_, _, Variant ts), qv -> return (stack, ts, qv)
                 | _ ->
                   Or_error.error_s
                     [%message
                       "variant.case requires a reference to a variant on the top of the \
                        stack"
                         ~actual_top:(t : Type.t)])
            in
            let%bind () =
              input_types |> List.map ~f:(Validity.type_valid f) |> Or_error.all_unit
            in
            let%bind () =
              output_types |> List.map ~f:(Validity.type_valid f) |> Or_error.all_unit
            in
            let%bind () =
              if Qual_leq.check f (QualC Lin) qv
              then return ()
              else
                Or_error.error_s
                  [%message
                    "variant.case requires a linear reference if the annotation is linear"
                      ~actual:(qv : Qual.t)]
            in
            let%bind inner_ess_and_ts =
              match List.zip inner_ess ts with
              | Ok l -> return l
              | Unequal_lengths ->
                Or_error.error_s
                  [%message
                    "variant.case had wrong number of cases"
                      ~num_cases:(List.length inner_ess : int)
                      ~types:(ts : Type.t list)]
            in
            let%bind stack, inner_annotated =
              let%bind f, framed_out = frame f stack input_types in
              let f = Function_ctx.add_label output_types l' f in
              let%bind inner_annotated =
                List.map inner_ess_and_ts ~f:(fun (inner_es, inner_t) ->
                  let%bind inner_annotated, actual_output_and_l'' =
                    has_type_instruction s c f l inner_es (inner_t :: input_types)
                  in
                  let%bind () =
                    match actual_output_and_l'' with
                    | None -> return ()
                    | Some (actual_output, l'') ->
                      let%bind () =
                        if List.equal Type.equal output_types actual_output
                        then return ()
                        else
                          error_s
                            [%message
                              "variant.case did not return the annotated types"
                                ~expected:(output_types : Type.t list)
                                ~got:(actual_output : Type.t list)]
                      in
                      let%bind () =
                        if Local_ctx.equal l' l''
                        then return ()
                        else
                          error_s
                            [%message
                              "variant.case did not have annotated local effect"
                                ~expected:(l' : Local_ctx.t)
                                ~got:(l'' : Local_ctx.t)]
                      in
                      return ()
                  in
                  return inner_annotated)
                |> Or_error.all
              in
              return (output_types @ framed_out, inner_annotated)
            in
            let%bind es, typ = has_type_instruction s c f l' es stack in
            return
              ( Ii.IVariantCase
                  (q_mem_type, ts, (input_types, output_types), tl, inner_annotated)
                :: es
              , typ ))
       | IArrayMalloc q ->
         let%bind stack, typ =
           match stack with
           | (Num (Int (U, I32)), _) :: t :: stack -> return (stack, t)
           | _ ->
             Or_error.error_s
               [%message
                 "array.malloc requires a stack with an i32 and another type on top"
                   ~actual_stack:(stack : Type.t list)]
         in
         let%bind () = Validity.qual_valid f q in
         let%bind () =
           let%bind b = Heapability.no_caps_type f typ in
           if b || Qual_leq.check f (QualC Lin) q
           then return ()
           else
             Or_error.error_s
               [%message
                 "array.malloc called with type containing caps" ~type_:(typ : Type.t)]
         in
         let%bind () =
           if Qual_leq.check f (snd typ) (QualC Unr)
           then return ()
           else
             Or_error.error_s
               [%message
                 "array.malloc given non-unrestricted value" ~qualifier:(snd typ : Qual.t)]
         in
         let type_for_annotation = typ in
         let typ = Substitution.Loc.incr_unbound_in_t 1 typ in
         let return_type : Type.t = ExLoc (Ref (W, LocV 0, Array typ), q), q in
         let%bind es, typ = has_type_instruction s c f l es (return_type :: stack) in
         return (Ii.IArrayMalloc (q, type_for_annotation) :: es, typ)
       | IArrayGet ->
         let%bind stack, typ =
           match stack with
           | (Num (Int (U, I32)), _) :: (Ref (_, _, Array typ), _) :: _ ->
             return (List.drop stack 1, typ)
           | _ ->
             Or_error.error_s
               [%message
                 "array.get requires a stack with an i32 and an array reference on the \
                  top of the stack"
                   ~actual_stack:(stack : Type.t list)]
         in
         let type_for_annotation = typ in
         let%bind es, typ = has_type_instruction s c f l es (typ :: stack) in
         return (Ii.IArrayGet type_for_annotation :: es, typ)
       | IArraySet ->
         let%bind stack, typ =
           match stack with
           | typ1 :: (Num (Int (U, I32)), _) :: (Ref (W, _, Array typ2), _) :: _
             when Type.equal typ1 typ2 -> return (List.drop stack 2, typ1)
           | _ ->
             Or_error.error_s
               [%message
                 "array.set requires a stack with a type, an i32, and a writable \
                  reference to an array of that type on the top of the stack"
                   ~actual_stack:(stack : Type.t list)]
         in
         let type_for_annotation = typ in
         let%bind es, typ = has_type_instruction s c f l es stack in
         return (Ii.IArraySet type_for_annotation :: es, typ)
       | IArrayFree ->
         let%bind stack, typ, q_ref =
           match stack with
           | (Ref (W, _, Array typ), q_ref) :: stack -> return (stack, typ, q_ref)
           | _ ->
             Or_error.error_s
               [%message
                 "array.free requires a stack with a writable reference to an array on \
                  the top of the stack"
                   ~actual_stack:(stack : Type.t list)]
         in
         let%bind () =
           if Qual_leq.check f (QualC Lin) q_ref
           then return ()
           else
             Or_error.error_s
               [%message
                 "attempted to free a potentially non-linear array"
                   ~qualifier:(q_ref : Qual.t)]
         in
         let type_for_annotation = typ in
         let%bind es, typ = has_type_instruction s c f l es stack in
         return (Ii.IArrayFree type_for_annotation :: es, typ)
       | IExistPack (pt, ht, q) ->
         let%bind qual_bound, size_bound, (heap_pt, heap_q) =
           match ht with
           | Ex (q, sz, (pt, hq)) -> return (q, sz, (pt, hq))
           | _ ->
             Or_error.error_s
               [%message
                 "exist.pack must be annotated with an existential type"
                   ~actual_heaptype_annotation:(ht : Type.ht)]
         in
         let return_type : Type.t = ExLoc (Ref (W, LocV 0, ht), q), q in
         let%bind () =
           if Qual.equal qual_bound q
           then return ()
           else
             Or_error.error_s
               [%message
                 "annotated qualifier must be the same as qual bound on exist.pack"]
         in
         let%bind () = Validity.type_valid f return_type in
         let%bind () = Validity.qual_valid f q in
         let%bind () = Validity.type_valid f (pt, q) in
         let%bind () = Validity.size_valid f size_bound in
         let%bind () =
           if Qual_leq.check f heap_q q
           then return ()
           else
             Or_error.error_s
               [%message
                 "qualifier of memory was less than qualifier of contained value for \
                  exist.pack"
                   ~contained_value:(heap_q : Qual.t)
                   ~mem:(q : Qual.t)]
         in
         let%bind size_of_witness =
           Sizing.size_of_type (Function_ctx.size_bounds_of_types f) (pt, q)
         in
         let%bind () =
           if Size_leq.check f size_of_witness size_bound
           then return ()
           else
             Or_error.error_s
               [%message
                 "size of pretype was not smaller than witness bound for exist.pack"
                   ~bound:(size_bound : Size.t)
                   ~size_of_witness:(size_of_witness : Size.t)]
         in
         let%bind () =
           let%bind b = Heapability.no_caps_pretype f pt in
           if b
           then return ()
           else
             Or_error.error_s
               [%message
                 "exist.pack witness has capabilities and is thus not heapable"
                   ~witness:(pt : Type.pt)]
         in
         let%bind f' = Function_ctx.add_constraint (Type (q, size_bound, Heapable)) f in
         let%bind () = Validity.type_valid f' (heap_pt, heap_q) in
         let%bind () =
           let%bind b = Heapability.no_caps_type f' (heap_pt, heap_q) in
           if b || Qual_leq.check f (QualC Lin) q
           then return ()
           else
             Or_error.error_s
               [%message
                 "exist.pack annotated heap type has capabilities and is thus not \
                  heapable"
                   ~annotated:((heap_pt, heap_q) : Type.t)]
         in
         let%bind stack, typ_to_pack =
           match stack with
           | [] -> Or_error.error_s [%message "exist.pack requires non-empty stack"]
           | t :: stack -> return (stack, t)
         in
         let substituted_with_witness =
           (heap_pt, heap_q) |> Substitution.Type.subst_in_t pt
         in
         let%bind () =
           if Type.equal typ_to_pack substituted_with_witness
           then return ()
           else
             Or_error.error_s
               [%message
                 "top of stack for exist.pack was not equal to the heaptype substituted \
                  with the witness type"
                   ~actual_top:(typ_to_pack : Type.t)
                   ~expected:(substituted_with_witness : Type.t)]
         in
         let%bind es, typ = has_type_instruction s c f l es (return_type :: stack) in
         return (Ii.IExistPack (pt, ht, q) :: es, typ)
       | IExistUnpack (q_mem_type, (input_types, output_types), tl, inner_es) ->
         let%bind () = Validity.qual_valid f q_mem_type in
         (match
            ( Qual_leq.check f q_mem_type (QualC Unr)
            , Qual_leq.check f (QualC Lin) q_mem_type )
          with
          | false, false ->
            Or_error.error_s
              [%message
                "exist.unpack qual annotation could not be determined to be linear or \
                 unrestricted"]
          | true, true ->
            raise_s
              [%message
                "BUG: qualifier was determined to be both linear and unrestricted"]
          | true, false ->
            let shift_types = List.map ~f:(Substitution.Type.incr_unbound_in_t 1) in
            let shift_locals =
              List.map ~f:(fun (t, sz) -> Substitution.Type.incr_unbound_in_t 1 t, sz)
            in
            let%bind l' = Local_ctx.apply_local_effect tl l in
            let%bind stack, sz_bound, q_bound, inner_t, qv, ref_typ_to_return =
              match stack with
              | [] -> Or_error.error_s [%message "exist.unpack requires non-empty stack"]
              | t :: stack ->
                (match t with
                 | Ref (_, _, Ex (sz_bound, q_bound, inner_t)), qv ->
                   return (stack, sz_bound, q_bound, inner_t, qv, t)
                 | _ ->
                   Or_error.error_s
                     [%message
                       "exist.unpack requires a reference to an existential on the top \
                        of the stack"
                         ~actual_top:(t : Type.t)])
            in
            let%bind () =
              input_types |> List.map ~f:(Validity.type_valid f) |> Or_error.all_unit
            in
            let%bind () =
              output_types |> List.map ~f:(Validity.type_valid f) |> Or_error.all_unit
            in
            let%bind () =
              if Qual_leq.check f (snd inner_t) (QualC Unr)
              then return ()
              else
                Or_error.error_s
                  [%message
                    "Contents of existential for exist.unpack must be unrestricted if \
                     the annotation is unrestricted"
                      ~actual:(snd inner_t : Qual.t)]
            in
            let%bind stack, inner_annotated =
              let%bind f, framed_out = frame f stack input_types in
              let f = Function_ctx.add_frame_constraint qv f in
              let f = Function_ctx.add_label output_types l' f in
              let%bind f =
                Function_ctx.add_constraint (Type (sz_bound, q_bound, Heapable)) f
              in
              let l = shift_locals l in
              let input_types = shift_types input_types in
              let%bind inner_annotated, actual_output_and_l'' =
                has_type_instruction s c f l inner_es (inner_t :: input_types)
              in
              let%bind () =
                match actual_output_and_l'' with
                | None -> return ()
                | Some (actual_output, l'') ->
                  let%bind () =
                    let output_types = shift_types output_types in
                    if List.equal Type.equal output_types actual_output
                    then return ()
                    else
                      error_s
                        [%message
                          "exist.unpack did not return the annotated types"
                            ~expected:(output_types : Type.t list)
                            ~got:(actual_output : Type.t list)]
                  in
                  let%bind () =
                    let l' = shift_locals l' in
                    if Local_ctx.equal l' l''
                    then return ()
                    else
                      error_s
                        [%message
                          "exist.unpack did not have annotated local effect"
                            ~expected:(l' : Local_ctx.t)
                            ~got:(l'' : Local_ctx.t)]
                  in
                  return ()
              in
              return (output_types @ [ ref_typ_to_return ] @ framed_out, inner_annotated)
            in
            let%bind es, typ = has_type_instruction s c f l' es stack in
            return
              ( Ii.IExistUnpack
                  (q_mem_type, (input_types, output_types), tl, inner_annotated, inner_t)
                :: es
              , typ )
          | false, true ->
            let shift_types = List.map ~f:(Substitution.Type.incr_unbound_in_t 1) in
            let shift_locals =
              List.map ~f:(fun (t, sz) -> Substitution.Type.incr_unbound_in_t 1 t, sz)
            in
            let%bind l' = Local_ctx.apply_local_effect tl l in
            let%bind stack, sz_bound, q_bound, inner_t, qv =
              match stack with
              | [] -> Or_error.error_s [%message "exist.unpack requires non-empty stack"]
              | t :: stack ->
                (match t with
                 | Ref (_, _, Ex (sz_bound, q_bound, inner_t)), qv ->
                   return (stack, sz_bound, q_bound, inner_t, qv)
                 | _ ->
                   Or_error.error_s
                     [%message
                       "exist.unpack requires a reference to an existential on the top \
                        of the stack"
                         ~actual_top:(t : Type.t)])
            in
            let%bind () =
              input_types |> List.map ~f:(Validity.type_valid f) |> Or_error.all_unit
            in
            let%bind () =
              output_types |> List.map ~f:(Validity.type_valid f) |> Or_error.all_unit
            in
            let%bind () =
              if Qual_leq.check f (QualC Lin) qv
              then return ()
              else
                Or_error.error_s
                  [%message
                    "exist.unpack requires a linear reference if the annotation is linear"
                      ~actual:(qv : Qual.t)]
            in
            let%bind stack, inner_annotated =
              let%bind f, framed_out = frame f stack input_types in
              let f = Function_ctx.add_label output_types l' f in
              let%bind f =
                Function_ctx.add_constraint (Type (sz_bound, q_bound, Heapable)) f
              in
              let l = shift_locals l in
              let input_types = shift_types input_types in
              let%bind inner_annotated, actual_output_and_l'' =
                has_type_instruction s c f l inner_es (inner_t :: input_types)
              in
              let%bind () =
                match actual_output_and_l'' with
                | None -> return ()
                | Some (actual_output, l'') ->
                  let%bind () =
                    let output_types = shift_types output_types in
                    if List.equal Type.equal output_types actual_output
                    then return ()
                    else
                      error_s
                        [%message
                          "exist.unpack did not return the annotated types"
                            ~expected:(output_types : Type.t list)
                            ~got:(actual_output : Type.t list)]
                  in
                  let%bind () =
                    let l' = shift_locals l' in
                    if Local_ctx.equal l' l''
                    then return ()
                    else
                      error_s
                        [%message
                          "exist.unpack did not have annotated local effect"
                            ~expected:(l' : Local_ctx.t)
                            ~got:(l'' : Local_ctx.t)]
                  in
                  return ()
              in
              return (output_types @ framed_out, inner_annotated)
            in
            let%bind es, typ = has_type_instruction s c f l' es stack in
            return
              ( Ii.IExistUnpack
                  (q_mem_type, (input_types, output_types), tl, inner_annotated, inner_t)
                :: es
              , typ ))
       | IRefSplit ->
         let%bind rw, loc, ht, q, stack =
           match List.hd stack with
           | Some (Ref (rw, loc, ht), q) ->
             let%bind () =
               if Qual_leq.check f (QualC Lin) q
               then return ()
               else
                 error_s
                   [%message
                     "Can only split linear references" ~reference_qualifier:(q : Qual.t)]
             in
             return (rw, loc, ht, q, List.tl_exn stack)
           | Some type_ ->
             error_s [%message "Ref split requires a reference" ~got:(type_ : Type.t)]
           | None -> error_s [%message "Ref split requires a non-empty stack"]
         in
         let%bind es, typ =
           has_type_instruction
             s
             c
             f
             l
             es
             ((Ptr loc, QualC Unr) :: (Cap (rw, loc, ht), q) :: stack)
         in
         return (Ii.IRefSplit :: es, typ)
       | IRefJoin ->
         let open Loc in
         let%bind rw, loc, ht, q, stack =
           match List.take stack 2 with
           | [ (Ptr (LocV n2), QualC Unr); (Cap (rw, LocV n1, ht), q) ] when n1 = n2 ->
             return (rw, LocV n1, ht, q, List.drop stack 2)
           | _ ->
             error_s
               [%message
                 "Ref join requires a matching capability and unrestrcted pointer on top \
                  of the stack"
                   ~got:(stack : Type.t list)]
         in
         let%bind es, typ =
           has_type_instruction s c f l es ((Ref (rw, loc, ht), q) :: stack)
         in
         return (Ii.IRefJoin :: es, typ)
       | IQualify new_q ->
         let%bind stack =
           match stack with
           | (Cap _, _) :: _ | (Ref _, _) :: _ ->
             error_s [%message "Qualify cannot be used on references or capabilities"]
           | (pt, old_q) :: stack ->
             let%bind () =
               if Qual_leq.check f old_q new_q
               then return ()
               else
                 error_s
                   [%message
                     "Qualify would potentially decrease linearity"
                       ~current_qualifier:(old_q : Qual.t)
                       ~new_qualifier:(new_q : Qual.t)]
             in
             return ((pt, new_q) :: stack)
           | [] -> error_s [%message "Qualify requires a non-empty stack"]
         in
         let%bind es, typ = has_type_instruction s c f l es stack in
         return (Ii.IQualify new_q :: es, typ))
  ;;

  let typecheck_and_annotate es s c f l = has_type_instruction s c f l es []
end

module Typecheck_function : sig
  val get_purported_type_and_exports : Instruction.f -> Type.ft * Ex.t list

  val verify_function_type_and_annotate
    :  Instruction.f
    -> Store_typing.t
    -> Module_type.t
    -> Ii.f Or_error.t
end = struct
  let get_purported_type_and_exports = function
    | Instruction.Fun (exports, fun_type, _, _) | FunIm (exports, fun_type, _) ->
      fun_type, exports
  ;;

  let verify_function_type_and_annotate (f : Instruction.f) (s : Store_typing.t) c
    : Ii.f Or_error.t
    =
    match f with
    | Fun (ex, fun_type, locals, es) ->
      let%bind () = Validity.fun_type_valid Function_ctx.empty fun_type in
      let kind_vars, (inputs, outputs) = fun_type in
      let%bind f =
        List.fold_left kind_vars ~init:(return Function_ctx.empty) ~f:(fun f kv ->
          let%bind f = f in
          Function_ctx.add_constraint kv f)
      in
      let f = Function_ctx.set_ret outputs f in
      let%bind l =
        (let%map l =
           List.map inputs ~f:(fun typ_ ->
             let%map size =
               Sizing.size_of_type (Function_ctx.size_bounds_of_types f) typ_
             in
             typ_, size)
           |> Or_error.all
         in
         l @ List.map locals ~f:(fun size -> (Type.Unit, QualC Unr), size))
        |> Or_error.tag_s ~tag:[%message "Failed to take sizes of pretype arguments"]
      in
      let%bind () = List.map locals ~f:(Validity.size_valid f) |> Or_error.all_unit in
      let%bind annotated, stack_and_l' =
        let es = strip_unreachable_code es in
        Typecheck_instruction.typecheck_and_annotate es s c f l
      in
      let%bind () =
        match stack_and_l' with
        | None -> return ()
        | Some (stack, l') ->
          let%bind () =
            List.map l' ~f:(fun ((_, q), _) ->
              if Qual_leq.check f q (QualC Unr)
              then return ()
              else
                Or_error.error_s
                  [%message
                    "Qual on type in local at end of function was not unrestricted"
                      (q : Qual.t)])
            |> Or_error.all_unit
          in
          let%bind () =
            let stack = List.rev stack in
            if List.equal Type.equal outputs stack
            then return ()
            else
              error_s
                [%message
                  "incorrect body type"
                    ~expected:(outputs : Type.t list)
                    ~got:(stack : Type.t list)]
          in
          return ()
      in
      return (Ii.Fun (ex, fun_type, locals, annotated))
    | FunIm (ex, fun_type, import) ->
      let (Import (import_module, name)) = import in
      let import_type =
        let%bind.Option module_type = Map.find s import_module in
        let%bind.Option import_index = Map.find module_type.func_exports name in
        List.nth module_type.funcs import_index
      in
      let%bind () =
        match import_type with
        | Some import_type ->
          if [%equal: Type.ft] fun_type import_type
          then return ()
          else
            error_s
              [%message
                "Function import type doesn't match"
                  ~expected:(fun_type : Type.ft)
                  ~got:(import_type : Type.ft)]
        | None -> error_s [%message "Function import not found" (import : Im.t)]
      in
      return (Ii.FunIm (ex, fun_type, import))
  ;;
end

module Typecheck_global : sig
  val get_purported_type_and_exports : Glob.t -> GlobalType.t * Ex.t list

  val verify_global_type_and_annotate
    :  Glob.t
    -> Store_typing.t
    -> Module_type.t
    -> Interface.Glob.t Or_error.t
end = struct
  let get_purported_type_and_exports = function
    | Glob.GlobMut (type_, _) -> (true, type_), []
    | GlobEx (exports, type_, _) | GlobIm (exports, type_, _) -> (false, type_), exports
  ;;

  let verify_global_type_and_annotate (g : Glob.t) (s : Store_typing.t) c
    : Interface.Glob.t Or_error.t
    =
    match g with
    | GlobMut (type_, es) | GlobEx (_, type_, es) ->
      let%bind annotated, stack_and_l =
        let es = strip_unreachable_code es in
        Typecheck_instruction.typecheck_and_annotate es s c Function_ctx.empty []
      in
      (match stack_and_l with
       | None -> Or_error.error_s [%message "Global has unreachable code"]
       | Some (stack, l) ->
         let%bind () =
           if List.length l <> 0
           then
             error_s
               [%message
                 "Internal invariant violated: non-empty local context returned while \
                  typechecking global"]
           else return ()
         in
         let%bind () =
           if List.equal Type.equal [ type_, QualC Unr ] stack
           then return ()
           else
             error_s
               [%message
                 "incorrect initialization type"
                   ~expected:([ type_, QualC Unr ] : Type.t list)
                   ~got:(stack : Type.t list)]
         in
         (match g with
          | GlobMut (type_, _) -> return (Interface.Glob.GlobMut (type_, annotated))
          | GlobEx (ex, type_, _) -> return (Interface.Glob.GlobEx (ex, type_, annotated))
          | GlobIm _ ->
            raise_s [%message "BUG: match inside match didn't match for globals"]))
    | GlobIm (ex, type_, import) ->
      let (Import (import_module, name)) = import in
      let import_type =
        let%bind.Option module_type = Map.find s import_module in
        let%bind.Option import_index = Map.find module_type.glob_exports name in
        List.nth module_type.globs import_index
      in
      (match import_type with
       | Some (_mut, import_type) ->
         if [%equal: Type.pt] type_ import_type
         then return (Interface.Glob.GlobIm (ex, type_, import))
         else
           error_s
             [%message
               "Global import type doesn't match"
                 ~expected:(type_ : Type.pt)
                 ~got:(import_type : Type.pt)]
       | None -> error_s [%message "Global import not found" (import : Im.t)])
  ;;
end

module Typecheck_module : sig
  val get_purported_type : Module.t -> Module_type.t Or_error.t

  val verify_module_type_and_annotate
    :  Module.t
    -> Store_typing.t
    -> Module_type.t
    -> Interface.Module.t Or_error.t
end = struct
  let get_purported_type (funcs, globs, table) =
    let funcs, func_exports_list =
      funcs |> List.map ~f:Typecheck_function.get_purported_type_and_exports |> List.unzip
    in
    let globs, glob_exports_list =
      globs |> List.map ~f:Typecheck_global.get_purported_type_and_exports |> List.unzip
    in
    let%bind table =
      List.map table ~f:(fun i ->
        match List.nth funcs i with
        | Some ft -> return ft
        | None -> error_s [%message "Invalid reference in table" ~reference:(i : int)])
      |> Or_error.all
    in
    let export_map_of_list export_list ~kind =
      let map_or_duplicates =
        export_list
        |> List.concat_mapi ~f:(fun index string_list ->
          List.map string_list ~f:(fun s -> s, index))
        |> String.Map.of_alist
      in
      match map_or_duplicates with
      | `Duplicate_key s -> error_s [%message "Duplicate export" ~kind ~name:(s : string)]
      | `Ok map -> return map
    in
    let%bind func_exports = export_map_of_list func_exports_list ~kind:"function" in
    let%bind glob_exports = export_map_of_list glob_exports_list ~kind:"global" in
    return { Module_type.funcs; globs; table; func_exports; glob_exports }
  ;;

  let verify_module_type_and_annotate (funcs, globs, table) s c =
    let%bind funcs =
      List.mapi funcs ~f:(fun function_index f ->
        Typecheck_function.verify_function_type_and_annotate f s c
        |> Or_error.tag_s
             ~tag:[%message "Failed to typecheck function" (function_index : int)])
      |> Or_error.all
    in
    let%bind globs =
      List.mapi globs ~f:(fun global_index g ->
        Typecheck_global.verify_global_type_and_annotate g s c
        |> Or_error.tag_s
             ~tag:[%message "Failed to typecheck global" (global_index : int)])
      |> Or_error.all
    in
    return (funcs, globs, table)
  ;;
end

let all_map m =
  m
  |> Map.to_alist
  |> List.map ~f:(fun (k, v) ->
    let%map v = v in
    k, v)
  |> Or_error.all
  |> Or_error.map ~f:String.Map.of_alist_exn
;;

let typecheck_and_annotate ms =
  let%bind types =
    Map.mapi ms ~f:(fun ~key:name ~data:m ->
      Typecheck_module.get_purported_type m
      |> Or_error.tag_s ~tag:[%message "Failed to typecheck module" (name : string)])
    |> all_map
  in
  let%bind annotated =
    Map.mapi ms ~f:(fun ~key:name ~data:m ->
      Typecheck_module.verify_module_type_and_annotate m types (Map.find_exn types name)
      |> Or_error.tag_s ~tag:[%message "Failed to typecheck module" (name : string)])
    |> all_map
  in
  return (annotated, types)
;;

let annotate ms = ms |> typecheck_and_annotate |> Or_error.map ~f:fst
let typecheck ms = ms |> typecheck_and_annotate |> Or_error.map ~f:snd
