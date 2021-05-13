import Logos.Prelude.Newtype
import Logos.Prelude.FunTypes

universe u
variable {P : Sort u}

namespace Logos 

--------------------------------------------------------------------------------
-- Constants
--------------------------------------------------------------------------------

class newtype Verum (P : Sort u) := export verum : P
class newtype Falsum (P : Sort u) := export falsum : P

@[defaultInstance low] instance iVerumOfProp : Verum Prop := pack True
@[defaultInstance low] instance iFalsumOfProp : Falsum Prop := pack False

--------------------------------------------------------------------------------
-- Connectives
--------------------------------------------------------------------------------

class funtype LArr (P : Sort u) := export larr : Binar P
class funtype SIff (P : Sort u) := export iff  : Binar P
class funtype Conj (P : Sort u) := export conj : Binar P
class funtype Disj (P : Sort u) := export disj : Binar P
class funtype LNeg (P : Sort u) := export lneg : Unar P

instance iLArrOfProp : LArr Prop := pack fun p q => p -> q
@[defaultInstance low] instance iSIffOfProp : SIff Prop := pack Iff
@[defaultInstance low] instance iConjOfProp : Conj Prop := pack And
@[defaultInstance low] instance iDisjOfProp : Disj Prop := pack Or
@[defaultInstance low] instance iLNegOfProp : LNeg Prop := pack Not

--------------------------------------------------------------------------------
-- Notation
--------------------------------------------------------------------------------

namespace Notation

scoped notation "⊤" => verum
scoped notation "⊥" => falsum

scoped infixr:25 " -> " => larr
scoped infixr:25 (priority := default + default) " ⇒ " => larr

scoped infix:20 " <-> " => iff
scoped infix:20 (priority := default + default) " ⇔ " => iff

scoped infixr:35 (priority := default + default) " /\\ " => conj
scoped infixr:35 (priority := default + default) " ∧ "   => conj
scoped infixr:30 (priority := default + default) " \\/ " => disj
scoped infixr:30 (priority := default + default) " ∨ "   => disj

scoped prefix:max (priority := default + default) "~" => lneg
scoped prefix:max (priority := default + default) "¬" => lneg
