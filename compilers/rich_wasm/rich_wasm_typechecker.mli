open! Core
open! Rich_wasm

val typecheck : Module.t String.Map.t -> Module_type.t String.Map.t Or_error.t

val annotate
  :  Module.t String.Map.t
  -> Rich_wasm_compiler_interface.Module.t String.Map.t Or_error.t
