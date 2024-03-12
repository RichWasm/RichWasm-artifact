open! Core
open! Syntax
open! Rich_wasm

val codegen
  :  Typechecked.Module.t
  -> source_printer:Source_printer.t
  -> Rich_wasm.Module.t Or_error.t
