namespace Gaea.Syntax

abbrev Zero (N : Type u) 
  := OfNat N (natLit! 0)

class Succ (N : Sort u) :=
  (S : N -> N)

end Gaea.Syntax
