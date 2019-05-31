type channel = int
type t = channel
let of_int x = x
let to_int ch = ch
let to_char c = Char.chr (Char.code 'c' + c)

let c = 0
let d = 1
let e = 2
let f = 3
let g = 4
let h = 5

module Map = SAList

type ('i,'o) io_map = { inputs : 'i Map.t ; outputs : 'o Map.t }
