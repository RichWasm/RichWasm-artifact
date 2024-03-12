export empty = fun [x]. -> 
  fold inj 0 ( + Unit, ( * x, Rec l. ( + Unit, ( * x, l)))) () as Rec l. ( + Unit, ( * x, l))
in
export cons = fun [x]. l : Rec l. ( + Unit, ( * x, l)), x : x ->
  fold inj 1 ( + Unit, ( * x, Rec l. ( + Unit, ( * x, l)))) ( * x, l)  as Rec l. ( + Unit, ( * x, l))
in
export iter_hd = fun [x]. l : Rec l. ( + Unit, ( * x, l)), f : (A []. x -> Unit) ->
  case l = unfold l in
  { (empty [x] ())
  ; let () = (f [] (proj 0 l)) in proj 1 l
  }
in
()
