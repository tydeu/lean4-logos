import Gaea.Newtype
import Gaea.FunTypes

universe u
variable {P : Sort u}

namespace Gaea 

--------------------------------------------------------------------------------
-- Constants
--------------------------------------------------------------------------------

class newtype Verum (P : Sort u) : P
class newtype Falsum (P : Sort u) : P

abbrev verum [K : Verum P] := unpack K
abbrev falsum [K : Falsum P] := unpack K

--------------------------------------------------------------------------------
-- Connectives
--------------------------------------------------------------------------------

class funtype LArr (P : Sort u) : Binar P
class funtype SIff (P : Sort u) : Binar P
class funtype Conj (P : Sort u) : Binar P
class funtype Disj (P : Sort u) : Binar P
class funtype LNeg (P : Sort u) : Unar P

abbrev larr [K : LArr P] := unpack K
abbrev iff  [K : SIff P] := unpack K
abbrev conj [K : Conj P] := unpack K
abbrev disj [K : Disj P] := unpack K
abbrev lneg [K : LNeg P] := unpack K

--------------------------------------------------------------------------------
-- Notation
--------------------------------------------------------------------------------

namespace Notation

scoped notation "⊤" => Verum.val
scoped notation "⊥" => Falsum.val

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
