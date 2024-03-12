open! Core
open! Syntax

val typecheck : Debruijned.Module.t 
  -> source_printer:Source_printer.t
  -> Typechecked.Module.t Or_error.t
