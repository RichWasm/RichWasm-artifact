global y = new_lin <Ref <( * Int, Int, Ref Int)>> in
export get_multiplier = fun []. r : Ref Int -> !r in
import rolling_averages.new_ : (A []. Ref Int -> <Ref <( * Int, Int, Ref Int)>>) in
import rolling_averages.add_sample : (A []. <Ref <( * Int, Int, Ref Int)>>, Int -> <Ref <( * Int, Int, Ref Int)>>) in
import rolling_averages.average : (A []. <Ref <( * Int, Int, Ref Int)>> -> <( * <Ref <( * Int, Int, Ref Int)>>, Int)>) in
let add_sample = fun []. i : Int -> (y := (add_sample [] (!y, i))) in
let average =  fun []. ->
  let (data, average) = (average [] (!y)) in
  let () = (y := data) in
  average
in
let multiplier = new 2 in
let () = (y := (new_ [] (multiplier))) in
let () = (add_sample [] (4)) in
let () = (multiplier := 6) in
let () = (add_sample [] (8)) in
let () = (multiplier := 10) in
let () = (add_sample [] (16)) in
if0 ( - (average [] ()) 12) then 1 else 0
