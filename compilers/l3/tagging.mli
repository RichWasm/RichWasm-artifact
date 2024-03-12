open! Core
open! Syntax

val tag : Source.Module.t -> Tagged.Module.t

val untag_t : Tagged.Type.t -> Source.Type.t

val untag_e : Tagged.Expr.t -> Source.Expr.t

val untag : Tagged.Module.t -> Source.Module.t
