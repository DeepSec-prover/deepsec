module List = struct

  include List

  let partition_unordered p l =
    let rec part yes no = function
    | [] -> yes, no
    | x :: l -> if p x then part (x :: yes) no l else part yes (x :: no) l in
    part [] [] l

  let filter_unordered p =
    let rec find accu = function
    | [] -> accu
    | x :: l -> if p x then find (x :: accu) l else find accu l in
    find []

end
