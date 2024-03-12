open! Core
open Rich_wasm

module type S = sig
  type t

  val incr_unbound_in_t : int -> Type.t -> Type.t
  val incr_unbound_in_pt : int -> Type.pt -> Type.pt
  val incr_unbound_in_ht : int -> Type.ht -> Type.ht
  val incr_unbound_in_at : int -> Type.at -> Type.at
  val incr_unbound_in_ft : int -> Type.ft -> Type.ft
  val subst_in_t : t -> Type.t -> Type.t
  val subst_in_pt : t -> Type.pt -> Type.pt
  val subst_in_at : t -> Type.at -> Type.at
  val subst_in_ft : t -> Type.ft -> Type.ft
end

module Qual = struct
  open Qual

  let incr_if_unbound ~depth incr q =
    match q with
    | QualV n -> if n < depth then QualV n else QualV (n + incr)
    | QualC _ -> q
  ;;

  let rec incr_unbound_in_t ~depth incr (pt, q) =
    incr_unbound_in_pt ~depth incr pt, incr_if_unbound ~depth incr q

  and incr_unbound_in_pt ~depth incr (pt : Type.pt) =
    match (pt : Type.pt) with
    | Num _ | Unit | Ptr _ | Own _ | Var _ -> pt
    | Prod ts -> ts |> List.map ~f:(incr_unbound_in_t ~depth incr) |> Prod
    | Coderef ft -> Coderef (incr_unbound_in_ft ~depth incr ft)
    | Rec (q, t) -> Rec (incr_if_unbound ~depth incr q, incr_unbound_in_t ~depth incr t)
    | ExLoc t -> ExLoc (incr_unbound_in_t ~depth incr t)
    | Cap (c, l, ht) -> Cap (c, l, incr_unbound_in_ht ~depth incr ht)
    | Ref (c, l, ht) -> Ref (c, l, incr_unbound_in_ht ~depth incr ht)

  and incr_unbound_in_ht ~depth incr ht =
    match ht with
    | Variant ts -> ts |> List.map ~f:(incr_unbound_in_t ~depth incr) |> Variant
    | Struct ts ->
      ts |> List.map ~f:(fun (t, sz) -> incr_unbound_in_t ~depth incr t, sz) |> Struct
    | Array t -> Array (incr_unbound_in_t ~depth incr t)
    | Ex (q, sz, t) ->
      Ex (incr_if_unbound ~depth incr q, sz, incr_unbound_in_t ~depth incr t)

  and incr_unbound_in_at ~depth incr (ts1, ts2) =
    let f = List.map ~f:(incr_unbound_in_t ~depth incr) in
    f ts1, f ts2

  and incr_unbound_in_ft ~depth incr (kvs, at) =
    let depth, kvs =
      List.fold_map kvs ~init:depth ~f:(fun depth kv ->
        match (kv : KindVar.t) with
        | Loc | Size _ -> depth, kv
        | Type (q, sz, h) -> depth, Type (incr_if_unbound ~depth incr q, sz, h)
        | Qual (qs1, qs2) ->
          let f = incr_if_unbound ~depth incr in
          depth + 1, Qual (List.map ~f qs1, List.map ~f qs2))
    in
    kvs, incr_unbound_in_at ~depth incr at
  ;;

  let incr_unbound_in_t = incr_unbound_in_t ~depth:0
  let incr_unbound_in_pt = incr_unbound_in_pt ~depth:0
  let incr_unbound_in_ht = incr_unbound_in_ht ~depth:0
  let incr_unbound_in_at = incr_unbound_in_at ~depth:0
  let incr_unbound_in_ft = incr_unbound_in_ft ~depth:0

  let incr_q incr q =
    match q with
    | QualV n -> QualV (n + incr)
    | QualC _ -> q
  ;;

  let subst_in_q idx q_sub q =
    match q with
    | QualV n when n > idx -> QualV (n - 1)
    | QualV n when n = idx -> q_sub
    | QualC _ | QualV _ -> q
  ;;

  (* returns the substituted kind_var as well as the index increment *)
  let subst_in_kindvar idx q kv =
    match (kv : KindVar.t) with
    | Loc | Size _ -> kv, 0
    | Type (qual, sz, hc) -> Type (subst_in_q idx q qual, sz, hc), 0
    | Qual (qs1, qs2) ->
      let f = List.map ~f:(subst_in_q idx q) in
      Qual (f qs1, f qs2), 1
  ;;

  let rec subst_in_t idx q (pt, qual) = subst_in_pt idx q pt, subst_in_q idx q qual

  and subst_in_pt idx q pt =
    match (pt : Type.pt) with
    | Num _ | Var _ | Unit | Ptr _ | Own _ -> pt
    | Prod ts -> ts |> List.map ~f:(subst_in_t idx q) |> Prod
    | Coderef ft -> Coderef (subst_in_ft idx q ft)
    | Rec (qual, t) -> Rec (subst_in_q idx q qual, subst_in_t idx q t)
    | ExLoc t -> ExLoc (subst_in_t idx q t)
    | Cap (c, l, ht) -> Cap (c, l, subst_in_ht idx q ht)
    | Ref (c, l, ht) -> Ref (c, l, subst_in_ht idx q ht)

  and subst_in_ht idx q ht =
    match ht with
    | Variant ts -> ts |> List.map ~f:(subst_in_t idx q) |> Variant
    | Struct ts -> ts |> List.map ~f:(fun (t, sz) -> subst_in_t idx q t, sz) |> Struct
    | Array t -> Array (subst_in_t idx q t)
    | Ex (qual, sz, t) -> Ex (subst_in_q idx q qual, sz, subst_in_t idx q t)

  and subst_in_at idx q (ts1, ts2) =
    let f = List.map ~f:(subst_in_t idx q) in
    f ts1, f ts2

  and subst_in_ft idx q (kvs, at) =
    let kvs_rev, idx, q =
      List.fold kvs ~init:([], idx, q) ~f:(fun (kv_rev, idx, q) kv ->
        let kv, incr = subst_in_kindvar idx q kv in
        let idx = idx + incr in
        let q = incr_q incr q in
        kv :: kv_rev, idx, q)
    in
    List.rev kvs_rev, subst_in_at idx q at
  ;;

  let subst_in_t q t = subst_in_t 0 q t
  let subst_in_pt q pt = subst_in_pt 0 q pt
  let subst_in_at q at = subst_in_at 0 q at
  let subst_in_ft q ft = subst_in_ft 0 q ft
end

module Size = struct
  open Size

  let rec incr_if_unbound ~depth incr sz =
    match sz with
    | SizeC _ -> sz
    | SizeV n -> if n < depth then SizeV n else SizeV (n + incr)
    | SizeP (sz1, sz2) ->
      SizeP (incr_if_unbound ~depth incr sz1, incr_if_unbound ~depth incr sz2)
  ;;

  let rec incr_unbound_in_t ~depth incr (pt, q) = incr_unbound_in_pt ~depth incr pt, q

  and incr_unbound_in_pt ~depth incr (pt : Type.pt) =
    match (pt : Type.pt) with
    | Num _ | Unit | Ptr _ | Own _ | Var _ -> pt
    | Prod ts -> ts |> List.map ~f:(incr_unbound_in_t ~depth incr) |> Prod
    | Coderef ft -> Coderef (incr_unbound_in_ft ~depth incr ft)
    | Rec (q, t) -> Rec (q, incr_unbound_in_t ~depth incr t)
    | ExLoc t -> ExLoc (incr_unbound_in_t ~depth incr t)
    | Cap (c, l, ht) -> Cap (c, l, incr_unbound_in_ht ~depth incr ht)
    | Ref (c, l, ht) -> Ref (c, l, incr_unbound_in_ht ~depth incr ht)

  and incr_unbound_in_ht ~depth incr ht =
    match ht with
    | Variant ts -> ts |> List.map ~f:(incr_unbound_in_t ~depth incr) |> Variant
    | Struct ts ->
      ts
      |> List.map ~f:(fun (t, sz) ->
           incr_unbound_in_t ~depth incr t, incr_if_unbound ~depth incr sz)
      |> Struct
    | Array t -> Array (incr_unbound_in_t ~depth incr t)
    | Ex (q, sz, t) ->
      Ex (q, incr_if_unbound ~depth incr sz, incr_unbound_in_t ~depth incr t)

  and incr_unbound_in_at ~depth incr (ts1, ts2) =
    let f = List.map ~f:(incr_unbound_in_t ~depth incr) in
    f ts1, f ts2

  and incr_unbound_in_ft ~depth incr (kvs, at) =
    let depth, kvs =
      List.fold_map kvs ~init:depth ~f:(fun depth kv ->
        match (kv : KindVar.t) with
        | Loc | Qual _ -> depth, kv
        | Type (q, sz, h) -> depth, Type (q, incr_if_unbound ~depth incr sz, h)
        | Size (szs1, szs2) ->
          let f = incr_if_unbound ~depth incr in
          depth + 1, Size (List.map ~f szs1, List.map ~f szs2))
    in
    kvs, incr_unbound_in_at ~depth incr at
  ;;

  let incr_unbound_in_t = incr_unbound_in_t ~depth:0
  let incr_unbound_in_pt = incr_unbound_in_pt ~depth:0
  let incr_unbound_in_ht = incr_unbound_in_ht ~depth:0
  let incr_unbound_in_at = incr_unbound_in_at ~depth:0
  let incr_unbound_in_ft = incr_unbound_in_ft ~depth:0

  let rec incr_sz incr sz =
    match sz with
    | SizeV n -> SizeV (n + incr)
    | SizeP (sz1, sz2) -> SizeP (incr_sz incr sz1, incr_sz incr sz2)
    | SizeC _ -> sz
  ;;

  let rec subst_in_sz idx sz_sub sz =
    match sz with
    | SizeV n when n > idx -> SizeV (n - 1)
    | SizeV n when n = idx -> sz_sub
    | SizeP (sz1, sz2) ->
      let f = subst_in_sz idx sz_sub in
      SizeP (f sz1, f sz2)
    | SizeC _ | SizeV _ -> sz
  ;;

  (* returns the substituted kind_var as well as the index increment *)
  let subst_in_kindvar idx sz kv =
    match (kv : KindVar.t) with
    | Loc | Qual _ -> kv, 0
    | Type (q, size, hc) -> Type (q, subst_in_sz idx sz size, hc), 0
    | Size (szs1, szs2) ->
      let f = List.map ~f:(subst_in_sz idx sz) in
      Size (f szs1, f szs2), 1
  ;;

  let rec subst_in_t idx sz (pt, q) = subst_in_pt idx sz pt, q

  and subst_in_pt idx sz pt =
    match (pt : Type.pt) with
    | Num _ | Var _ | Unit | Ptr _ | Own _ -> pt
    | Prod ts -> ts |> List.map ~f:(subst_in_t idx sz) |> Prod
    | Coderef ft -> Coderef (subst_in_ft idx sz ft)
    | Rec (q, t) -> Rec (q, subst_in_t idx sz t)
    | ExLoc t -> ExLoc (subst_in_t idx sz t)
    | Cap (c, l, ht) -> Cap (c, l, subst_in_ht idx sz ht)
    | Ref (c, l, ht) -> Ref (c, l, subst_in_ht idx sz ht)

  and subst_in_ht idx sz ht =
    match ht with
    | Variant ts -> ts |> List.map ~f:(subst_in_t idx sz) |> Variant
    | Struct ts ->
      ts
      |> List.map ~f:(fun (t, size) -> subst_in_t idx sz t, subst_in_sz idx sz size)
      |> Struct
    | Array t -> Array (subst_in_t idx sz t)
    | Ex (q, size, t) -> Ex (q, subst_in_sz idx sz size, subst_in_t idx sz t)

  and subst_in_at idx sz (ts1, ts2) =
    let f = List.map ~f:(subst_in_t idx sz) in
    f ts1, f ts2

  and subst_in_ft idx sz (kvs, at) =
    let kvs_rev, idx, sz =
      List.fold kvs ~init:([], idx, sz) ~f:(fun (kv_rev, idx, sz) kv ->
        let kv, incr = subst_in_kindvar idx sz kv in
        let idx = idx + incr in
        let sz = incr_sz incr sz in
        kv :: kv_rev, idx, sz)
    in
    List.rev kvs_rev, subst_in_at idx sz at
  ;;

  let subst_in_t sz t = subst_in_t 0 sz t
  let subst_in_pt sz pt = subst_in_pt 0 sz pt
  let subst_in_at sz at = subst_in_at 0 sz at
  let subst_in_ft sz ft = subst_in_ft 0 sz ft
end

module Loc = struct
  open Loc

  let incr_if_unbound ~depth incr l =
    match l with
    | LocV n -> if n < depth then LocV n else LocV (n + incr)
  ;;

  let rec incr_unbound_in_t ~depth incr (pt, q) = incr_unbound_in_pt ~depth incr pt, q

  and incr_unbound_in_pt ~depth incr (pt : Type.pt) =
    match (pt : Type.pt) with
    | Num _ | Unit | Var _ -> pt
    | Prod ts -> ts |> List.map ~f:(incr_unbound_in_t ~depth incr) |> Prod
    | Coderef ft -> Coderef (incr_unbound_in_ft ~depth incr ft)
    | Rec (q, t) -> Rec (q, incr_unbound_in_t ~depth incr t)
    | Ptr l -> Ptr (incr_if_unbound ~depth incr l)
    | Own l -> Own (incr_if_unbound ~depth incr l)
    | Cap (c, l, ht) ->
      Cap (c, incr_if_unbound ~depth incr l, incr_unbound_in_ht ~depth incr ht)
    | Ref (c, l, ht) ->
      Ref (c, incr_if_unbound ~depth incr l, incr_unbound_in_ht ~depth incr ht)
    | ExLoc t -> ExLoc (incr_unbound_in_t ~depth:(depth + 1) incr t)

  and incr_unbound_in_ht ~depth incr ht =
    match ht with
    | Variant ts -> ts |> List.map ~f:(incr_unbound_in_t ~depth incr) |> Variant
    | Struct ts ->
      ts |> List.map ~f:(fun (t, sz) -> incr_unbound_in_t ~depth incr t, sz) |> Struct
    | Array t -> Array (incr_unbound_in_t ~depth incr t)
    | Ex (q, sz, t) -> Ex (q, sz, incr_unbound_in_t ~depth incr t)

  and incr_unbound_in_at ~depth incr (ts1, ts2) =
    let f = List.map ~f:(incr_unbound_in_t ~depth incr) in
    f ts1, f ts2

  and incr_unbound_in_ft ~depth incr (kvs, at) =
    let depth, kvs =
      List.fold_map kvs ~init:depth ~f:(fun depth kv ->
        match (kv : KindVar.t) with
        | Qual _ | Size _ | Type _ -> depth, kv
        | Loc -> depth + 1, Loc)
    in
    kvs, incr_unbound_in_at ~depth incr at
  ;;

  let incr_unbound_in_t = incr_unbound_in_t ~depth:0
  let incr_unbound_in_pt = incr_unbound_in_pt ~depth:0
  let incr_unbound_in_ht = incr_unbound_in_ht ~depth:0
  let incr_unbound_in_at = incr_unbound_in_at ~depth:0
  let incr_unbound_in_ft = incr_unbound_in_ft ~depth:0

  let incr_l incr l =
    match l with
    | LocV n -> LocV (n + incr)
  ;;

  let subst_in_l idx l_sub l =
    match l with
    | LocV n when n > idx -> LocV (n - 1)
    | LocV n when n = idx -> l_sub
    | LocV _ -> l
  ;;

  let is_loc kv =
    match (kv : KindVar.t) with
    | Qual _ | Size _ | Type _ -> false
    | Loc -> true
  ;;

  let rec subst_in_t idx l (pt, q) = subst_in_pt idx l pt, q

  and subst_in_pt idx l pt =
    match (pt : Type.pt) with
    | Num _ | Var _ | Unit -> pt
    | Prod ts -> ts |> List.map ~f:(subst_in_t idx l) |> Prod
    | Coderef ft -> Coderef (subst_in_ft idx l ft)
    | Rec (q, t) -> Rec (q, subst_in_t idx l t)
    | Ptr loc -> Ptr (subst_in_l idx l loc)
    | ExLoc t -> ExLoc (subst_in_t idx l t)
    | Own loc -> Own (subst_in_l idx l loc)
    | Cap (c, loc, ht) -> Cap (c, subst_in_l idx l loc, subst_in_ht idx l ht)
    | Ref (c, loc, ht) -> Ref (c, subst_in_l idx l loc, subst_in_ht idx l ht)

  and subst_in_ht idx l ht =
    match ht with
    | Variant ts -> ts |> List.map ~f:(subst_in_t idx l) |> Variant
    | Struct ts -> ts |> List.map ~f:(fun (t, sz) -> subst_in_t idx l t, sz) |> Struct
    | Array t -> Array (subst_in_t idx l t)
    | Ex (q, sz, t) -> Ex (q, sz, subst_in_t idx l t)

  and subst_in_at idx l (ts1, ts2) =
    let f = List.map ~f:(subst_in_t idx l) in
    f ts1, f ts2

  and subst_in_ft idx l (kvs, at) =
    let incr = List.count kvs ~f:is_loc in
    let idx = idx + incr in
    let l = incr_l incr l in
    kvs, subst_in_at idx l at
  ;;

  let subst_in_t l t = subst_in_t 0 l t
  let subst_in_pt l pt = subst_in_pt 0 l pt
  let subst_in_at l at = subst_in_at 0 l at
  let subst_in_ft l ft = subst_in_ft 0 l ft
end

module Type = struct
  open Type

  let is_type kv =
    match (kv : KindVar.t) with
    | Loc | Size _ | Qual _ -> false
    | Type _ -> true
  ;;

  let rec incr_unbound_in_t ~depth incr (pt, q) = incr_unbound_in_pt ~depth incr pt, q

  and incr_unbound_in_pt ~depth incr pt =
    match (pt : Type.pt) with
    | Var n -> if n < depth then Var n else Var (n + incr)
    | Num _ | Unit | Ptr _ | Own _ -> pt
    | Prod ts -> ts |> List.map ~f:(incr_unbound_in_t ~depth incr) |> Prod
    | Coderef ft -> Coderef (incr_unbound_in_ft ~depth incr ft)
    | Rec (q, t) -> Rec (q, incr_unbound_in_t ~depth:(depth + 1) incr t)
    | ExLoc t -> ExLoc (incr_unbound_in_t ~depth incr t)
    | Cap (c, l, ht) -> Cap (c, l, incr_unbound_in_ht ~depth incr ht)
    | Ref (c, l, ht) -> Ref (c, l, incr_unbound_in_ht ~depth incr ht)

  and incr_unbound_in_ht ~depth incr ht =
    match ht with
    | Variant ts -> ts |> List.map ~f:(incr_unbound_in_t ~depth incr) |> Variant
    | Struct ts ->
      ts |> List.map ~f:(fun (t, sz) -> incr_unbound_in_t ~depth incr t, sz) |> Struct
    | Array t -> Array (incr_unbound_in_t ~depth incr t)
    | Ex (q, sz, t) -> Ex (q, sz, incr_unbound_in_t ~depth:(depth + 1) incr t)

  and incr_unbound_in_at ~depth incr (ts1, ts2) =
    let f = List.map ~f:(incr_unbound_in_t ~depth incr) in
    f ts1, f ts2

  and incr_unbound_in_ft ~depth incr (kvs, at) =
    let depth = depth + List.count kvs ~f:is_type in
    kvs, incr_unbound_in_at ~depth incr at
  ;;

  let incr_unbound_in_t = incr_unbound_in_t ~depth:0
  let incr_unbound_in_pt = incr_unbound_in_pt ~depth:0
  let incr_unbound_in_ht = incr_unbound_in_ht ~depth:0
  let incr_unbound_in_at = incr_unbound_in_at ~depth:0
  let incr_unbound_in_ft = incr_unbound_in_ft ~depth:0

  let rec subst_in_t idx pt (pretype, q) = subst_in_pt idx pt pretype, q

  and subst_in_pt idx pt pretype =
    match (pretype : Type.pt) with
    | Var n when n > idx -> Var (n - 1)
    | Var n when n = idx -> pt
    | Num _ | Unit | Var _ | Ptr _ | Own _ -> pretype
    | Prod ts -> ts |> List.map ~f:(subst_in_t idx pt) |> Prod
    | Coderef ft -> Coderef (subst_in_ft idx pt ft)
    | Rec (q, t) -> Rec (q, subst_in_t (idx + 1) (incr_unbound_in_pt 1 pt) t)
    | ExLoc t -> ExLoc (subst_in_t idx (Loc.incr_unbound_in_pt 1 pt) t)
    | Cap (c, l, ht) -> Cap (c, l, subst_in_ht idx pt ht)
    | Ref (c, l, ht) -> Ref (c, l, subst_in_ht idx pt ht)

  and subst_in_ht idx pt ht =
    match ht with
    | Variant ts -> ts |> List.map ~f:(subst_in_t idx pt) |> Variant
    | Struct ts -> ts |> List.map ~f:(fun (t, sz) -> subst_in_t idx pt t, sz) |> Struct
    | Array t -> Array (subst_in_t idx pt t)
    | Ex (q, sz, t) -> Ex (q, sz, subst_in_t (idx + 1) (incr_unbound_in_pt 1 pt) t)

  and subst_in_at idx pt (ts1, ts2) =
    let f = List.map ~f:(subst_in_t idx pt) in
    f ts1, f ts2

  and subst_in_ft idx pt (kvs, at) =
    let pt =
      List.fold_left kvs ~init:pt ~f:(fun pt kv ->
        match (kv : KindVar.t) with
        | Loc -> Loc.incr_unbound_in_pt 1 pt
        | Qual _ -> Qual.incr_unbound_in_pt 1 pt
        | Size _ -> Size.incr_unbound_in_pt 1 pt
        | Type _ -> incr_unbound_in_pt 1 pt)
    in
    let incr = List.count kvs ~f:is_type in
    kvs, subst_in_at (idx + incr) pt at
  ;;

  let subst_in_t pt t = subst_in_t 0 pt t
  let subst_in_pt pt pretype = subst_in_pt 0 pt pretype
  let subst_in_at pt at = subst_in_at 0 pt at
  let subst_in_ft pt ft = subst_in_ft 0 pt ft
end

open! Core

let main_example_type =
  let open Rich_wasm in
  let open Qual in
  let open Size in
  let open Type in
  let open Loc in
  let types =
    [ Unit, QualV 0
    ; Rec (QualV 1, (Unit, QualV 0)), QualV 3
    ; ( Coderef
          ( [ KindVar.Loc
            ; Loc
            ; Qual ([], [])
            ; Qual ([ QualV 0; QualV 1 ], [ QualV 0; QualV 1 ])
            ; Size ([], [])
            ; Size ([ SizeV 0; SizeP (SizeV 0, SizeV 1) ], [])
            ; Type (QualV 0, SizeV 0, Heapable)
            ; Type (QualV 2, SizeV 2, Heapable)
            ]
          , ( [ Var 0, QualV 2; Var 1, QualV 0; Var 2, QualV 1 ]
            , [ ( Cap
                    ( R
                    , LocV 0
                    , Struct
                        [ (Unit, QualC Unr), SizeV 1
                        ; (Ptr (LocV 1), QualC Lin), SizeC 2
                        ; (Own (LocV 2), QualC Lin), SizeC 2
                        ] )
                , QualV 0 )
              ] ) )
      , QualV 1 )
    ]
  in
  Prod types, QualC Unr
;;

let%expect_test "loc test" =
  print_s [%sexp (Loc.subst_in_t (LocV 20) main_example_type : Rich_wasm.Type.t)];
  [%expect
    {|
    ((Prod
      ((Unit (QualV 0)) ((Rec (QualV 1) (Unit (QualV 0))) (QualV 3))
       ((Coderef
         ((Loc Loc (Qual () ())
           (Qual ((QualV 0) (QualV 1)) ((QualV 0) (QualV 1))) (Size () ())
           (Size ((SizeV 0) (SizeP (SizeV 0) (SizeV 1))) ())
           (Type (QualV 0) (SizeV 0) Heapable)
           (Type (QualV 2) (SizeV 2) Heapable))
          ((((Var 0) (QualV 2)) ((Var 1) (QualV 0)) ((Var 2) (QualV 1)))
           (((Cap R (LocV 0)
              (Struct
               (((Unit (QualC Unr)) (SizeV 1))
                (((Ptr (LocV 1)) (QualC Lin)) (SizeC 2))
                (((Own (LocV 22)) (QualC Lin)) (SizeC 2)))))
             (QualV 0))))))
        (QualV 1))))
     (QualC Unr)) |}]
;;

let%expect_test "qual test" =
  print_s [%sexp (Qual.subst_in_t (QualV 20) main_example_type : Rich_wasm.Type.t)];
  [%expect
    {|
    ((Prod
      ((Unit (QualV 20)) ((Rec (QualV 0) (Unit (QualV 20))) (QualV 2))
       ((Coderef
         ((Loc Loc (Qual () ())
           (Qual ((QualV 0) (QualV 21)) ((QualV 0) (QualV 21))) (Size () ())
           (Size ((SizeV 0) (SizeP (SizeV 0) (SizeV 1))) ())
           (Type (QualV 0) (SizeV 0) Heapable)
           (Type (QualV 22) (SizeV 2) Heapable))
          ((((Var 0) (QualV 22)) ((Var 1) (QualV 0)) ((Var 2) (QualV 1)))
           (((Cap R (LocV 0)
              (Struct
               (((Unit (QualC Unr)) (SizeV 1))
                (((Ptr (LocV 1)) (QualC Lin)) (SizeC 2))
                (((Own (LocV 2)) (QualC Lin)) (SizeC 2)))))
             (QualV 0))))))
        (QualV 0))))
     (QualC Unr)) |}]
;;

let%expect_test "size test" =
  print_s [%sexp (Size.subst_in_t (SizeV 20) main_example_type : Rich_wasm.Type.t)];
  [%expect
    {|
    ((Prod
      ((Unit (QualV 0)) ((Rec (QualV 1) (Unit (QualV 0))) (QualV 3))
       ((Coderef
         ((Loc Loc (Qual () ())
           (Qual ((QualV 0) (QualV 1)) ((QualV 0) (QualV 1))) (Size () ())
           (Size ((SizeV 0) (SizeP (SizeV 0) (SizeV 21))) ())
           (Type (QualV 0) (SizeV 0) Heapable)
           (Type (QualV 2) (SizeV 22) Heapable))
          ((((Var 0) (QualV 2)) ((Var 1) (QualV 0)) ((Var 2) (QualV 1)))
           (((Cap R (LocV 0)
              (Struct
               (((Unit (QualC Unr)) (SizeV 1))
                (((Ptr (LocV 1)) (QualC Lin)) (SizeC 2))
                (((Own (LocV 2)) (QualC Lin)) (SizeC 2)))))
             (QualV 0))))))
        (QualV 1))))
     (QualC Unr)) |}]
;;

let%expect_test "type test" =
  print_s [%sexp (Type.subst_in_t (Var 20) main_example_type : Rich_wasm.Type.t)];
  [%expect
    {|
    ((Prod
      ((Unit (QualV 0)) ((Rec (QualV 1) (Unit (QualV 0))) (QualV 3))
       ((Coderef
         ((Loc Loc (Qual () ())
           (Qual ((QualV 0) (QualV 1)) ((QualV 0) (QualV 1))) (Size () ())
           (Size ((SizeV 0) (SizeP (SizeV 0) (SizeV 1))) ())
           (Type (QualV 0) (SizeV 0) Heapable)
           (Type (QualV 2) (SizeV 2) Heapable))
          ((((Var 0) (QualV 2)) ((Var 1) (QualV 0)) ((Var 22) (QualV 1)))
           (((Cap R (LocV 0)
              (Struct
               (((Unit (QualC Unr)) (SizeV 1))
                (((Ptr (LocV 1)) (QualC Lin)) (SizeC 2))
                (((Own (LocV 2)) (QualC Lin)) (SizeC 2)))))
             (QualV 0))))))
        (QualV 1))))
     (QualC Unr)) |}]
;;

let%expect_test "mega test" =
  print_s
    [%sexp
      (Type.subst_in_t
         (Coderef
            ( [ Type (QualV 0, SizeV 0, Heapable) ]
            , ([ Ref (R, LocV 0, Struct [ (Var 0, QualV 0), SizeV 0 ]), QualC Unr ], [])
            ))
         main_example_type
        : Rich_wasm.Type.t)];
  [%expect
    {|
    ((Prod
      ((Unit (QualV 0)) ((Rec (QualV 1) (Unit (QualV 0))) (QualV 3))
       ((Coderef
         ((Loc Loc (Qual () ())
           (Qual ((QualV 0) (QualV 1)) ((QualV 0) (QualV 1))) (Size () ())
           (Size ((SizeV 0) (SizeP (SizeV 0) (SizeV 1))) ())
           (Type (QualV 0) (SizeV 0) Heapable)
           (Type (QualV 2) (SizeV 2) Heapable))
          ((((Var 0) (QualV 2)) ((Var 1) (QualV 0))
            ((Coderef
              (((Type (QualV 2) (SizeV 2) Heapable))
               ((((Ref R (LocV 2) (Struct ((((Var 0) (QualV 2)) (SizeV 2)))))
                  (QualC Unr)))
                ())))
             (QualV 1)))
           (((Cap R (LocV 0)
              (Struct
               (((Unit (QualC Unr)) (SizeV 1))
                (((Ptr (LocV 1)) (QualC Lin)) (SizeC 2))
                (((Own (LocV 2)) (QualC Lin)) (SizeC 2)))))
             (QualV 0))))))
        (QualV 1))))
     (QualC Unr)) |}]
;;

let%expect_test "rec test" =
  let open Rich_wasm.Type in
  let inner_pretype =
    ExLoc
      ( Ref
          ( W
          , LocV 0
          , Variant
              [ Unit, QualC Unr; Prod [ Var 1, QualC Unr; Var 0, QualC Unr ], QualC Unr ]
          )
      , QualC Unr )
  in
  let rec_pretype = Rec (QualC Unr, (inner_pretype, QualC Unr)) in
  print_s
    [%sexp (Type.subst_in_t rec_pretype (inner_pretype, QualC Unr) : Rich_wasm.Type.t)];
  [%expect {|
    ((ExLoc
      ((Ref W (LocV 0)
        (Variant
         ((Unit (QualC Unr))
          ((Prod
            (((Var 0) (QualC Unr))
             ((Rec (QualC Unr)
               ((ExLoc
                 ((Ref W (LocV 0)
                   (Variant
                    ((Unit (QualC Unr))
                     ((Prod (((Var 1) (QualC Unr)) ((Var 0) (QualC Unr))))
                      (QualC Unr)))))
                  (QualC Unr)))
                (QualC Unr)))
              (QualC Unr))))
           (QualC Unr)))))
       (QualC Unr)))
     (QualC Unr)) |}]
;;
