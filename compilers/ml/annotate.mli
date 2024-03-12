open! Core
open! Syntax

val annotate
  :  Hoisted.Module.t
  -> source_printer:Source_printer.t
  -> Annotated.Module.t Or_error.t
