import Gaea.Logic.Fun.Types

universe u
variable {P : Sort u}

namespace Gaea.Logic 

--------------------------------------------------------------------------------
-- Constants
--------------------------------------------------------------------------------

class Verum (P : Sort u) :=
  toProp : P

abbrev verum [K : Verum P] := K.toProp

class Falsum (P : Sort u) :=
  toProp : P

abbrev falsum [K : Falsum P] := K.toProp

--------------------------------------------------------------------------------
-- Connectives
--------------------------------------------------------------------------------

class LArr (P : Sort u) :=
  toFun : Binar P

abbrev larr [K : LArr P] := K.toFun

namespace LArr
abbrev funType (K : LArr P) := Binar P
instance : CoeFun (LArr P) funType := {coe := fun K => K.toFun}
end LArr

class SIff (P : Sort u) :=
  toFun : Binar P

abbrev iff [K : SIff P] := K.toFun

namespace SIff
abbrev funType (K : SIff P) := Binar P
instance : CoeFun (SIff P) funType := {coe := fun K => K.toFun}
end SIff

class Conj (P : Sort u) :=
  toFun : Binar P

abbrev conj [K : Conj P] := K.toFun

namespace Conj
abbrev funType (K : Conj P) := Binar P
instance : CoeFun (Conj P) funType := {coe := fun K => K.toFun}
end Conj

class Disj (P : Sort u) :=
  toFun : Binar P

abbrev disj [K : Disj P] := K.toFun

namespace Disj
abbrev funType (K : Disj P) := Binar P
instance : CoeFun (Disj P) funType := {coe := fun K => K.toFun}
end Disj

class LNeg (P : Sort u) :=
  toFun : Unar P

abbrev lneg [K : LNeg P] := K.toFun

namespace LNeg
abbrev funType (K : LNeg P) := Unar P
instance : CoeFun (LNeg P) funType := {coe := fun K => K.toFun}
end LNeg

--------------------------------------------------------------------------------
-- Notation
--------------------------------------------------------------------------------

namespace Notation

scoped notation "⊤" => Verum.toProp
scoped notation "⊥" => Falsum.toProp

scoped infixr:25 " -> "  => LArr.toFun
scoped infixr:25 " ⇒ "   => LArr.toFun

scoped infix:20 " <-> "  => SIff.toFun
scoped infix:20 " ⇔ "   => SIff.toFun

scoped infixr:35 " /\\ " => Conj.toFun
scoped infixr:35 " ∧ "   => Conj.toFun
scoped infixr:30 " \\/ " => Disj.toFun
scoped infixr:30 " ∨ "   => Disj.toFun

scoped prefix:max "~"    => LNeg.toFun
scoped prefix:max "¬"    => LNeg.toFun
