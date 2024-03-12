open! Core

module type S = sig
  val check : unit -> bool

  module Qual : sig
    type t

    val of_qual : Rich_wasm.Qual.t -> t
    val assume_leq : less:t -> greater:t -> unit
    val assume_eq : t -> t -> unit
    val check_leq : less:t -> greater:t -> unit
  end

  module Size : sig
    type t

    val of_size : Rich_wasm.Size.t -> t
    val assume_leq : less:t -> greater:t -> unit
    val assume_eq : t -> t -> unit
    val check_leq : less:t -> greater:t -> unit
  end
end

val create_constraint_checker : unit -> (module S)
