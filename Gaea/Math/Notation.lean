import Gaea.Math.Syntax

open Gaea.Math

-- Functions

export Gaea.Math.Succ (S)

-- Operators

infix:50 " < "  => LT.lt
infix:50 " <= " => LE.le
infix:50 " ≤ "  => LE.le

-- Natural Literals

instance (N : Type u) [K : Zero N] : OfNat N (natLit! 0)
  := {ofNat := K.zero}

instance (N : Type u) [K : One N] : OfNat N (natLit! 1)
  := {ofNat := K.one}

instance (N : Type u) [K : Succ N] (n : Nat) [T : OfNat N n] 
  : OfNat N (Nat.succ n) := {ofNat := K.succ T.ofNat}
