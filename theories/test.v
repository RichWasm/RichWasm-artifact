

CoInductive stream (T: Set): Set :=
  Cons: T -> stream T -> stream T.

CoFixpoint map_stream {T : Set} (f : T -> T) (s : stream T) :=
  match s with
  | Cons _ h t => Cons T (f h) (map_stream f t)
  end.

Require Import Extraction.

Recursive Extraction map_stream. 


(*

(* Prints : *)

type 't stream = 't __stream Lazy.t
and 't __stream =
| Cons of 't * 't stream

(** val map_stream :
    ('a1 -> 'a1) -> 'a1 stream -> 'a1 stream **)

let rec map_stream f s =
  let Cons (h, t) = Lazy.force s in
  lazy (Cons ((f h), (map_stream f t)))


 *)



Inductive aexp : Type :=
| Num : nat -> aexp
| Plus : aexp -> aexp -> aexp.


Fixpoint step (a : aexp) : option aexp :=
  match a with
  | Num _ => None
  | Plus (Num a1) (Num a2) =>
    Some (Num (a1 + a1))
  | Plus a1 a2 =>
    match step a1 with
    | Some a1' => Some (Plus a1' a2)
    | None => match step a2 with
              | Some a2' => Some (Plus a1 a2')
              | None => None
              end
    end
  end.



Inductive type : Type :=
| TUnit
| TLam : type -> type -> type.


Fixpoint denote_type (t : type) : Type :=
  match t with
  | TUnit => unit
  | TLam t1 t2 => (denote_type t1) -> (denote_type t2)
  end.


Inductive exp : Type :=
| Unit
| Var : nat -> exp 
| Lam : nat -> exp -> exp
| App : exp -> exp -> exp. 


Fixpoint denote (tenv : nat -> type) (env : forall x, denote_type (tenv x))
         (e : exp) (t : type) : denote_type t :=



() -> ()      ====>      fun (_ : unit) => () 

() -> () -> ()  ====>    fun (_ : unit) => fun (_ : unit) => () 
