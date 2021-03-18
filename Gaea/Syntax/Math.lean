namespace Gaea.Syntax

-- Numerics

-- abbrev Zero (N : Type u) 
--   := OfNat N (natLit! 0)

class Zero (N : Sort u) :=
  (zero : N)

@[defaultInstance 1]
instance (N : Type u) [K : Zero N] : OfNat N (natLit! 0)
  := {ofNat := K.zero}

class One (N : Sort u) :=
  (one : N)

@[defaultInstance 1]
instance (N : Type u) [K : One N] : OfNat N (natLit! 1)
  := {ofNat := K.one}

class Succ (N : Sort u) :=
  (succ : N -> N)

namespace Succ
abbrev S {N : Sort u} [K : Succ N] := K.succ
end Succ

instance (N : Type u) [K : Succ N] (n : Nat) [T : OfNat N n] 
  : OfNat N (Nat.succ n) := {ofNat := K.succ T.ofNat}

-- Inequalities

class LT (P : Sort u) (N : Sort v) :=
  (lt : N -> N -> P)

class LE (P : Sort u) (N : Sort v)  :=
  (le : N -> N -> P)

end Gaea.Syntax
