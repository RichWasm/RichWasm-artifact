open! Core
open! Syntax
open Angstrom
open Let_syntax

let illegal_identifiers =
  [ "import"
  ; "let"
  ; "in"
  ; "dupl"
  ; "drop"
  ; "new"
  ; "free"
  ; "swap"
  ; "join"
  ; "split"
  ; "fun"
  ; "I"
  ; "E"
  ; "A"
  ; "Ptr"
  ; "Cap"
  ; "Ref"
  ; "Int"
  ]
;;

let whitespace = skip_while Char.is_whitespace
let required_whitespace = take_while1 Char.is_whitespace >>| Fn.const ()
let number = take_while1 Char.is_digit >>| int_of_string
let name = take_while1 (fun c -> Char.(is_alphanum c || c = '_'))

let identifier =
  name
  >>= fun s ->
  match List.find illegal_identifiers ~f:(String.equal s) with
  | Some s -> fail [%string "Illegal identifier %{s}"]
  | None -> return s
;;

let binding_or_unit =
  choice [ (string "*" >>| fun _ -> `Unit); (identifier >>| fun s -> `Binding s) ]
;;

let list_ () = sep_by (char ',' *> whitespace)

module Type = struct
  open Source.Type

  let unit_ =
    let+ _ = char 'I' in
    Unit
  ;;

  let int_ =
    let+ _ = string "Int" in
    Int
  ;;

  let ptr =
    let+ s = string "Ptr" *> whitespace *> identifier in
    Ptr s
  ;;

  let type_ =
    fix (fun type_ ->
      let prod =
        let+ ts = char '<' *> list_ () type_ <* char '>' in
        Prod ts
      in
      let fun_ =
        let+ foralls =
          char '(' *> whitespace *> char 'A' *> whitespace *> list_ () identifier
          <* whitespace
          <* char '.'
        and+ args = list_ () type_ <* string "-o"
        and+ ret = type_ <* char ')' in
        Fun { foralls; args; ret }
      in
      let bang =
        let+ t = char '!' *> type_ in
        Bang t
      in
      let cap =
        let+ name = string "Cap" *> whitespace *> identifier
        and+ typ = type_
        and+ size = number in
        Cap (name, typ, size)
      in
      let ref =
        let+ nativity =
          string "Ref"
          *> whitespace
          *> option
               Nativity.Native
               (let+ _ = char '!' in
                Nativity.Foreign)
          <* whitespace
        and+ name = identifier
        and+ typ = type_
        and+ size = number in
        Ref (name, typ, size, nativity)
      in
      let exists =
        let+ name = char 'E' *> whitespace *> identifier <* whitespace <* char '.'
        and+ typ = type_ in
        Exists (name, typ)
      in
      whitespace
      *> choice
           ~failure_msg:"could not determine type"
           [ int_; unit_; prod; fun_; bang; ptr; cap; ref; exists ]
      <* whitespace)
  ;;

  let parse_type s =
    match parse_string ~consume:All type_ s with
    | Ok t -> t
    | Error s -> raise_s [%sexp (s : string)]
  ;;

  let f s = s |> parse_type |> sexp_of_t |> print_s

  let%expect_test "parse type" =
    f "<I, E r. (A s, d, f. Ptr r, Cap r I 3,  !I -o <I,I>)>";
    [%expect
      {|
      (Prod
       (Unit
        (Exists r
         (Fun (foralls (s d f)) (args ((Ptr r) (Cap r Unit 3) (Bang Unit)))
          (ret (Prod (Unit Unit))))))) |}]
  ;;

  let%expect_test "parse type" =
    f "Cap e Int 0";
    [%expect {| (Cap e Int 0) |}]
  ;;
end

module Expr = struct
  open Source.Expr

  let unit_ =
    let+ _ = char '*' in
    Unit
  ;;

  let var =
    let+ s = identifier in
    Var s
  ;;

  let int_ =
    let+ f = option Fn.id (char '-' |> map ~f:(fun _ -> Int.neg))
    and+ i = number in
    Int (f i)
  ;;

  let expr_ =
    fix (fun expr_ ->
      let binop =
        let+ op =
          char '(' *> required_whitespace *> choice [ char '+'; char '-'; char '*'; char '/' ]
        and+ t1 = expr_
        and+ t2 = expr_ <* char ')' in
        let op =
          match op with
          | '+' -> `Add
          | '-' -> `Sub
          | '*' -> `Mul
          | '/' -> `Div
          | _ -> raise_s [%message "Internal compiler invariant violated: binop parsing"]
        in
        Binop (t1, t2, op)
      in
      let let_unit =
        let+ bind =
          string "let" *> whitespace *> char '*' *> whitespace *> char '=' *> expr_
          <* string "in"
        and+ body = expr_ in
        LetUnit { bind; body }
      in
      let prod =
        let+ ts = char '<' *> list_ () expr_ <* char '>' in
        Prod ts
      in
      let let_prod =
        let+ vars =
          string "let" *> whitespace *> char '<' *> whitespace *> list_ () binding_or_unit
          <* whitespace
          <* char '>'
          <* whitespace
          <* char '='
        and+ bind = expr_ <* string "in"
        and+ body = expr_ in
        LetProd { vars; bind; body }
      in
      let apply =
        let+ f = char '(' *> expr_
        and+ args = list_ () expr_ <* char ')' in
        Apply { f; args }
      in
      let bang =
        let+ t = char '!' *> expr_ in
        Bang t
      in
      let let_bang =
        let+ var =
          string "let" *> whitespace *> char '!' *> whitespace *> binding_or_unit
          <* whitespace
          <* char '='
        and+ bind = expr_ <* string "in"
        and+ body = expr_ in
        LetBang { var; bind; body }
      in
      let dupl =
        let+ t = string "dupl" *> required_whitespace *> expr_ in
        Dupl t
      in
      let drop =
        let+ t = string "drop" *> required_whitespace *> expr_ in
        Drop t
      in
      let new_ =
        let+ e = string "new" *> required_whitespace *> expr_
        and+ n = number in
        New (e, n)
      in
      let free =
        let+ t = string "free" *> required_whitespace *> expr_ in
        Free t
      in
      let swap =
        let+ e1 = string "swap" *> required_whitespace *> expr_
        and+ e2 = expr_ in
        Swap (e1, e2)
      in
      let join =
        let+ t = string "join" *> required_whitespace *> expr_ in
        Join t
      in
      let split =
        let+ t = string "split" *> required_whitespace *> expr_ in
        Split t
      in
      let inst =
        let+ e = char '(' *> expr_
        and+ names =
          char '[' *> whitespace *> list_ () identifier
          <* whitespace
          <* char ']'
          <* whitespace
          <* char ')'
        in
        Inst (e, names)
      in
      let pack =
        let+ s = char '{' *> whitespace *> identifier <* whitespace <* char ','
        and+ e = expr_ <* char '}' in
        Pack (s, e)
      in
      let unpack =
        let+ locvar =
          string "let" *> whitespace *> char '{' *> whitespace *> identifier
          <* whitespace
          <* char ','
          <* whitespace
        and+ var = binding_or_unit <* whitespace <* char '}' <* whitespace <* char '='
        and+ package = expr_ <* string "in"
        and+ body = expr_ in
        Unpack { locvar; var; package; body }
      in
      whitespace
      *> choice
           ~failure_msg:"could not parse expr"
           [ unit_
           ; let_unit
           ; prod
           ; let_prod
           ; apply
           ; bang
           ; let_bang
           ; dupl
           ; drop
           ; new_
           ; free
           ; swap
           ; join
           ; split
           ; inst
           ; pack
           ; unpack
           ; binop
           ; int_
           ; var
           ]
      <* whitespace)
  ;;

  let parse_expr s =
    match parse_string ~consume:All expr_ s with
    | Ok t -> t
    | Error s -> raise_s [%sexp (s : string)]
  ;;

  let f s = s |> parse_expr |> sexp_of_t |> print_s

  let%expect_test "parse expr" =
    f
      {|
let* = * in
let<a, b, c >= <asdf, dupl *, drop *, new * 3, free *, swap swap * * * >in
let! d = !( * e f ) in
let{k, l}= {m, <*>} in
<*, <qwerty>, *>|};
    [%expect
      {|
      (LetUnit (bind Unit)
       (body
        (LetProd (vars ((Binding a) (Binding b) (Binding c)))
         (bind
          (Prod
           ((Var asdf) (Dupl Unit) (Drop Unit) (New Unit 3) (Free Unit)
            (Swap (Swap Unit Unit) Unit))))
         (body
          (LetBang (var (Binding d)) (bind (Bang (Binop (Var e) (Var f) Mul)))
           (body
            (Unpack (locvar k) (var (Binding l)) (package (Pack m (Prod (Unit))))
             (body (Prod (Unit (Prod ((Var qwerty))) Unit)))))))))) |}]
  ;;
end

module Module = struct
  open Source.Module

  let module_ =
    fix (fun module_ ->
      let import =
        let+ mod_name = string "import" *> required_whitespace *> identifier <* char '.'
        and+ fun_name = identifier <* whitespace <* char ':'
        and+ typ = Type.type_ <* string "in"
        and+ m = module_ in
        LetIm ({ typ; mod_name; fun_name }, m)
      in
      let export =
        let+ ex_name =
          string "export" *> whitespace *> identifier
          <* whitespace
          <* char '='
          <* whitespace
          <* char 'A'
          <* whitespace
        and+ foralls =
          list_ () identifier
          <* whitespace
          <* char '.'
          <* whitespace
          <* string "fun"
          <* required_whitespace
        and+ args =
          list_ () (both (binding_or_unit <* whitespace <* char ':') Type.type_)
          <* char '.'
        and+ body = Expr.expr_ <* string "in"
        and+ m = module_ in
        LetEx (ex_name, { foralls; args; body }, m)
      in
      let body =
        let+ e = Expr.expr_ in
        Body e
      in
      whitespace
      *> choice
           ~failure_msg:"could not parse module"
           [ import <?> "import"; export <?> "export"; body <?> "body" ]
      <* whitespace)
  ;;

  let parse_module s =
    match parse_string ~consume:All module_ s with
    | Ok t -> t
    | Error s -> raise_s [%sexp (s : string)]
  ;;

  let f s = s |> parse_module |> sexp_of_t |> print_s

  let%expect_test "parse module" =
    f
      {|
import MLmodule.functionexample : I in
export asdf = A l1, l2. fun x : I, y : <I>. let* = * in x in
let <x, y, z> = <*, functionexample, asdf> in *
    |};
    [%expect
      {|
      (LetIm ((typ Unit) (mod_name MLmodule) (fun_name functionexample))
       (LetEx asdf
        ((foralls (l1 l2)) (args (((Binding x) Unit) ((Binding y) (Prod (Unit)))))
         (body (LetUnit (bind Unit) (body (Var x)))))
        (Body
         (LetProd (vars ((Binding x) (Binding y) (Binding z)))
          (bind (Prod (Unit (Var functionexample) (Var asdf)))) (body Unit))))) |}]
  ;;

  let%expect_test "paper_exampe" =
    f
      {|
import ml.stash : !(A. E l. <Cap l !Int 1, !Ptr l> -o E l. <Cap l !Int 1, !Ptr l>) in
import ml.get_stashed : !(A. !I -o E l. <Cap l !Int 1, !Ptr l>) in
let! stash = stash in
let! get_stashed = get_stashed in
let {_,_} = free (stash new !1 1) in
free (get_stashed !*)
      |};
    [%expect
      {|
      (LetIm
       ((typ
         (Bang
          (Fun (foralls ())
           (args ((Exists l (Prod ((Cap l (Bang Int) 1) (Bang (Ptr l)))))))
           (ret (Exists l (Prod ((Cap l (Bang Int) 1) (Bang (Ptr l)))))))))
        (mod_name ml) (fun_name stash))
       (LetIm
        ((typ
          (Bang
           (Fun (foralls ()) (args ((Bang Unit)))
            (ret (Exists l (Prod ((Cap l (Bang Int) 1) (Bang (Ptr l)))))))))
         (mod_name ml) (fun_name get_stashed))
        (Body
         (LetBang (var (Binding stash)) (bind (Var stash))
          (body
           (LetBang (var (Binding get_stashed)) (bind (Var get_stashed))
            (body
             (Unpack (locvar _) (var (Binding _))
              (package
               (Free (Apply (f (Var stash)) (args ((New (Bang (Int 1)) 1))))))
              (body (Free (Apply (f (Var get_stashed)) (args ((Bang Unit)))))))))))))) |}]
  ;;
end

let parse = Module.parse_module

(* 
https://arthursonzogni.com/Diagon/#Grammar
{|
type = "I"
     | "Int"
     | "Ptr" identifier
     | "<" {type {"," type}} ">"
     | "(" "A" {identifier {"," identifier}} "." {type {"," type}} "-o" type ")"
     | "!" type
     | "Cap" identifier type natural
     | "Ref" ["!"] identifier type natural
     | "E" identifier "." type
.

binding = "*" | identifier .

typed_binding = binding ":" type .

binop = "+" | "-" | "*" | "/" .

expr = "*"
     | identifier
     | integer
     | "( " binop expr expr ")"
     | "let" "*" "=" expr "in" expr
     | "<" {expr {"," expr}} ">"
     | "let" "<" {binding {"," binding}} ">" "=" expr "in" expr
     | "(" expr {expr {"," expr}} ")"
     | "!" expr
     | "let" "!" binding "=" expr "in" expr
     | "dupl" expr
     | "drop" expr
     | "new" expr natural
     | "free" expr
     | "swap" expr expr
     | "join" expr
     | "split" expr
     | "(" expr "[" {identifier {"," identifier}} "]" ")"
     | "{" identifier "," expr "}"
     | "let" "{" identifier "," binding "}" "=" expr "in" expr
.

module = "import" identifier "." identifier ":" type "in" module
       | "export" identifier "=" "A" {identifier {"," identifier}} "." "fun" {binding {"," binding}} "." expr "in" module
       | expr
.
|}
*)

