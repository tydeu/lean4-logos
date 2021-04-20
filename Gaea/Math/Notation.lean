import Gaea.Math.Syntax

universe u

namespace Gaea.Math

-- Operators

scoped infix:50 " < "  => SLess.toFun
scoped infix:50 " <= " => SLessEq.toFun
scoped infix:50 " ≤ "  => SLessEq.toFun

scoped infixl:65 (priority := default + default) " + "  => SAdd.toFun
scoped infixl:70 (priority := default + default) " * "  => SMul.toFun

-- Functions

@[scoped appUnexpander Gaea.Math.S] 
def unexpandS : Lean.PrettyPrinter.Unexpander
  | `(Math.S $n) => `($(Lean.mkIdent `S) $n)
  | _  => throw ()

@[scoped appUnexpander Gaea.Math.Succ.toFun] 
def unexpandSucc : Lean.PrettyPrinter.Unexpander
  | `(Math.Succ.toFun $n) => `($(Lean.mkIdent `S) $n)
  | _  => throw ()

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
  : OfNatLit A (Nat.succ n) := {ofNatLit := K.toFun T.ofNatLit}

@[scoped macro numLit] 
def expandNumLit : Lean.Macro
  | n => `(OfNatLit.ofNatLit (natLit! $n))

@[scoped appUnexpander Gaea.Math.OfNatLit.ofNatLit] 
def unexpandNumLit : Lean.PrettyPrinter.Unexpander
  | `(Math.OfNatLit.ofNatLit $n:numLit) => n
  | _  => throw ()

end Gaea.Math
