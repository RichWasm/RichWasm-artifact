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

module Qual : S with type t := Qual.t
module Size : S with type t := Size.t
module Type : S with type t := Type.pt
module Loc : S with type t := Loc.t

