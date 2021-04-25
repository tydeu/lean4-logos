import Gaea.Logic.Rel.Type
import Gaea.Logic.Fun.Types

universes u v
variable {P : Sort u} {T : Sort v}

namespace Gaea

--------------------------------------------------------------------------------
-- Numerals
--------------------------------------------------------------------------------

-- Sort-polymorphic Natural Literals

class OfNatLit (A : Sort u) (n : Nat) :=
  ofNatLit : A

@[defaultInstance low]
instance iNatOfNatLit {n : Nat} : OfNatLit Nat n
  := {ofNatLit := n}

@[defaultInstance low + low]
instance iOfNatLitOfNat {A : Type u} {n : Nat} 
  [K : OfNat A n] : OfNatLit A n
  := {ofNatLit := K.ofNat}

instance iOfMatOfNatLit {A : Type u} {n : Nat} 
  [K : OfNatLit A n] : OfNat A n
  := {ofNat := K.ofNatLit}

-- Specializations

class abbrev Zero (T : Sort u) 
  := OfNatLit T (nat_lit 0)

namespace Zero
abbrev zero [K : Zero T] := K.ofNatLit
end Zero

instance ZeroOfNat : Zero Nat 
  := {ofNatLit := Nat.zero}

class abbrev One (T : Sort u) 
  := OfNatLit T (nat_lit 1)

namespace One
abbrev one [K : Zero T] := K.ofNatLit
end One

instance OneOfNat : One Nat 
  := {ofNatLit := Nat.succ Nat.zero}

class Succ (T : Sort u) :=
  toFun : Unar T

abbrev S [K : Succ T] := K.toFun

namespace Succ
abbrev funType (K : Succ T) := Unar T
instance : CoeFun (Succ T) funType := {coe := fun K => K.toFun}
end Succ

instance SuccOfNat : Succ Nat 
  := {toFun := Nat.succ}

instance (A : Sort u) [K : Succ A] (n : Nat) [T : OfNatLit A n] 
  : OfNatLit A (Nat.succ n) := {ofNatLit := K.toFun T.ofNatLit}

--------------------------------------------------------------------------------
-- Operations
--------------------------------------------------------------------------------

class SAdd (T : Sort v) :=
  toFun : Binar T

-- Currently causes Lean to panic, will be fixed in the April 26th nightly
-- instance iSAddOfAdd {T : Type v} 
--   [K : Add T] : SAdd T := {toFun := K.add} 

instance iAddOfSAdd {T : Type v} 
  [K : SAdd T] : Add T := {add := K.toFun} 

namespace SAdd
abbrev funType (K : SAdd T) := Binar T
instance : CoeFun (SAdd T) funType := {coe := fun K => K.toFun}
end SAdd

class SMul (T : Sort v) :=
  toFun : Binar T

-- Currently causes Lean to panic, will be fixed in the April 26th nightly
-- instance iSMulOfMul {T : Type v} 
--   [K : Mul T] : SMul T := {toFun := K.mul} 

instance iMulOfSMul {T : Type v} 
  [K : SMul T] : Mul T := {mul := K.toFun} 

namespace SMul
abbrev funType (K : SMul T) := Binar T
instance : CoeFun (SMul T) funType := {coe := fun K => K.toFun}
end SMul

--------------------------------------------------------------------------------
-- Inequalities
--------------------------------------------------------------------------------

class SLt (P : Sort u) (T : Sort v) :=
  toFun : Rel P T

namespace SLt
abbrev funType (K : SLt P T) := Rel P T
instance : CoeFun (SLt P T) funType := {coe := fun K => K.toFun}
end SLt

class SLe (P : Sort u) (T : Sort v)  :=
  toFun : Rel P T

namespace SLe
abbrev funType (K : SLe P T) := Rel P T
instance : CoeFun (SLe P T) funType := {coe := fun K => K.toFun}
end SLe

class SGt (P : Sort u) (T : Sort v) :=
  toFun : Rel P T

namespace SGt
abbrev funType (K : SGt P T) := Rel P T
instance : CoeFun (SGt P T) funType := {coe := fun K => K.toFun}
end SGt

class SGe (P : Sort u) (T : Sort v)  :=
  toFun : Rel P T

namespace SGe
abbrev funType (K : SGe P T) := Rel P T
instance : CoeFun (SGe P T) funType := {coe := fun K => K.toFun}
end SGe

--------------------------------------------------------------------------------
-- Notation
--------------------------------------------------------------------------------

namespace Notation

-- Operators

scoped infixl:65 (priority := default + default) " + "  => SAdd.toFun
scoped infixl:70 (priority := default + default) " * "  => SMul.toFun

-- Inequalities

scoped infix:50 (name := syntaxLt)  " < "  => SLt.toFun
scoped infix:50 (name := syntaxLe)  " <= " => SLe.toFun
scoped infix:50 (name := syntaxLe') " ≤ "  => SLe.toFun
scoped infix:50 (name := syntaxGt)  " > "  => SGt.toFun
scoped infix:50 (name := syntaxGe)  " >= " => SGe.toFun
scoped infix:50 (name := syntaxGe') " ≥ "  => SGe.toFun

macro_rules (kind := syntaxLt)  | `($x < $y)  => `(binrel% SLt.toFun $x $y)
macro_rules (kind := syntaxLe)  | `($x <= $y) => `(binrel% SLe.toFun $x $y)
macro_rules (kind := syntaxLe') | `($x ≤ $y)  => `(binrel% SGt.toFun $x $y)
macro_rules (kind := syntaxGt)  | `($x > $y)  => `(binrel% SGe.toFun $x $y)
macro_rules (kind := syntaxGe)  | `($x >= $y) => `(binrel% SGe.toFun $x $y)
macro_rules (kind := syntaxGe') | `($x ≥ $y)  => `(binrel% SGe.toFun $x $y)

-- Functions

@[scoped appUnexpander Gaea.Math.S] 
def unexpandS : Lean.PrettyPrinter.Unexpander
  | `($_x:ident $n) => `($(Lean.mkIdent `S) $n)
  | _  => throw ()

@[scoped appUnexpander Gaea.Math.Succ.toFun] 
def unexpandSucc : Lean.PrettyPrinter.Unexpander
  | `($_x:ident $n) => `($(Lean.mkIdent `S) $n)
  | _  => throw ()


-- Numerals

@[scoped macro numLit] 
def expandNumLit : Lean.Macro
  | n => `(OfNatLit.ofNatLit (nat_lit $n))

@[scoped appUnexpander Gaea.Math.OfNatLit.ofNatLit] 
def unexpandNumLit : Lean.PrettyPrinter.Unexpander
  | `(Math.OfNatLit.ofNatLit $n:numLit) => n
  | _  => throw ()
