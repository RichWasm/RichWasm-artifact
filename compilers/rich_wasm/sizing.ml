open! Core
open! Rich_wasm
open Or_error.Let_syntax
open Size

let rec size_of_type size_ctx (pt, _) = size_of_pretype size_ctx pt

and size_of_pretype size_ctx pt =
  match (pt : Type.pt) with
  | Num (Int (_, I32)) | Num (Float F32) -> return (SizeC 32)
  | Num (Int (_, I64)) | Num (Float F64) -> return (SizeC 64)
  | Var n ->
    (match List.nth size_ctx n with
     | None ->
       error_s [%message "Type variable is unbound in size calculation" ~var:(n : int)]
     | Some sz -> return sz)
  | Own _ | Cap _ | Unit -> return (SizeC 0)
  | Prod ts ->
    List.fold ts ~init:(return (SizeC 0)) ~f:(fun acc t ->
      let%bind acc = acc in
      let%bind size = size_of_type size_ctx t in
      return (SizeP (acc, size)))
  | Ptr _ | Coderef _ | Ref _ -> return (SizeC 64)
  | Rec (_, t) -> size_of_type (SizeC 0 :: size_ctx) t
  | ExLoc t -> size_of_type size_ctx t
;;
