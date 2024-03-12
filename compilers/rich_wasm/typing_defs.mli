open! Core
open Rich_wasm

module Local_ctx : sig
  type t = (Type.t * Size.t) list [@@deriving equal, sexp]

  val apply_local_effect : LocalEffect.t -> t -> t Or_error.t
end

module Function_ctx : sig
  type t

  val empty : t
  val add_constraint : KindVar.t -> t -> t Or_error.t
  val type_constraints : int -> t -> (Qual.t * Size.t * Heapable_const.t) Or_error.t
  val qual_solver : t -> (module Solver.S)
  val size_solver : t -> (module Solver.S)
  val size_bounds_of_types : t -> Size.t list
  val qual_bound : int -> t -> bool
  val size_bound : int -> t -> bool
  val loc_bound : int -> t -> bool
  val add_frame_constraint : Qual.t -> t -> t
  val new_frame : t -> t
  val set_ret : Type.t list -> t -> t
  val add_label : Type.t list -> Local_ctx.t -> t -> t
  val jump_requirements : int -> t -> (Type.t list * Local_ctx.t) Or_error.t
  val linear_requirements : int -> t -> Qual.t list Or_error.t
  val all_linear_requirements : t -> Qual.t list list
  val ret : t -> Type.t list option
end

module Store_typing : sig
  type t = Module_type.t String.Map.t [@@deriving sexp]
end
