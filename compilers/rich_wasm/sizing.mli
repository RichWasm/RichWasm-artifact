open! Core
open Rich_wasm

val size_of_type : Size.t list -> Type.t -> Size.t Or_error.t
val size_of_pretype : Size.t list -> Type.pt -> Size.t Or_error.t
