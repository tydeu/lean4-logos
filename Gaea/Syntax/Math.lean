namespace Gaea.Syntax

-- Numerics

abbrev Zero (N : Type u) 
  := OfNat N (natLit! 0)

class Succ (N : Sort u) :=
  (S : N -> N)

-- Inequalities

class LT (P : Sort u) (N : Sort v) :=
  (lt : N -> N -> P)

class LE (P : Sort u) (N : Sort v)  :=
  (le : N -> N -> P)

end Gaea.Syntax
