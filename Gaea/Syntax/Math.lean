namespace Gaea.Syntax

-- Numerics

-- abbrev Zero (N : Type u) 
--   := OfNat N (natLit! 0)

class Zero (N : Sort u) :=
  (zero : N)

instance (N : Type u) [C : Zero N] : OfNat N (natLit! 0)
  := {ofNat := C.zero}

class Succ (N : Sort u) :=
  (succ : N -> N)

namespace Succ
abbrev S {N : Sort u} [C : Succ N] := C.succ
end Succ

instance (N : Type u) [C : Succ N] (n : Nat) [T : OfNat N n] 
  : OfNat N (Nat.succ n) := {ofNat := C.succ T.ofNat}

-- Inequalities

class LT (P : Sort u) (N : Sort v) :=
  (lt : N -> N -> P)

class LE (P : Sort u) (N : Sort v)  :=
  (le : N -> N -> P)

end Gaea.Syntax
