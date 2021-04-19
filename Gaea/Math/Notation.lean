import Gaea.Math.Syntax

universe u

open Gaea.Math

-- Functions

export Gaea.Math.Succ (S)

-- Operators

infix:50 " < "  => LT.lt
infix:50 " <= " => LE.le
infix:50 " ≤ "  => LE.le

-- Sort-polymorphic Natural Literals

class OfNatLit (A : Sort u) (n : Nat) :=
  ofNatLit : A

@[defaultInstance low]
instance {A : Type u} {n : Nat} [K : OfNat A n] : OfNatLit A n
  := {ofNatLit := K.ofNat}

instance {A : Type u} {n : Nat} [K : OfNatLit A n] : OfNat A n
  := {ofNat := K.ofNatLit}

instance (A : Sort u) [K : Zero A] 
  : OfNatLit A (natLit! 0) := {ofNatLit := K.zero}

instance (A : Sort u) [K : One A] 
  : OfNatLit A (natLit! 1) := {ofNatLit := K.one}

instance (A : Sort u) [K : Succ A] (n : Nat) [T : OfNatLit A n] 
  : OfNatLit A (Nat.succ n) := {ofNatLit := K.succ T.ofNatLit}

syntax (name := sortNumLit) (priority := default + low) num : term
macro_rules [sortNumLit]
  | `( $n:numLit) => `(OfNatLit.ofNatLit (natLit! $n))
