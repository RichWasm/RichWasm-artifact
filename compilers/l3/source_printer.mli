open! Core
open! Syntax

type t

val create : Tagged.Module.t -> t
val get_source : t -> Tag.t -> string option
