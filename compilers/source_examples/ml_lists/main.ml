global y = new 0 in
import list.empty : (A [x]. -> Rec l. ( + Unit, ( * x, l))) in
import list.cons : (A [x].  Rec l. ( + Unit, ( * x, l)), x -> Rec l. ( + Unit, ( * x, l))) in
import list.iter_hd : (A [x]. Rec l. ( + Unit, ( * x, l)), (A []. x -> Unit) -> Rec l. ( + Unit, ( * x, l))) in
let l = (cons [Int] ((cons [Int] ((empty [Int] ()), 7)), 5)) in
let f = fun []. x : Int -> (y := ( + !y x )) in
let empty = (iter_hd [Int] ((iter_hd [Int] (l, f)), f)) in
!y
