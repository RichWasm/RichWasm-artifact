export get_multiplier = fun []. r : Ref Int -> !r in
import rolling_averages.new_ : (A []. Ref Int -> <Ref <( * Int, Int, Ref Int)>>) in
import rolling_averages.free_ : (A []. <Ref <( * Int, Int, Ref Int)>> -> Unit) in
import rolling_averages.add_sample : (A []. <Ref <( * Int, Int, Ref Int)>>, Int -> <Ref <( * Int, Int, Ref Int)>>) in
import rolling_averages.average : (A []. <Ref <( * Int, Int, Ref Int)>> -> <( * <Ref <( * Int, Int, Ref Int)>>, Int)>) in
let multiplier = new 2 in
let y = (new_ [] (multiplier)) in
let y = (add_sample [] (y, 4)) in
let () = (multiplier := 6) in
let y = (add_sample [] (y, 8)) in
let () = (multiplier := 10) in
let y = (add_sample [] (y, 16)) in
let (y, average) = (average [] (y)) in
let () = (free_ [] (y)) in
if0 ( - average 12) then 0 else 42
