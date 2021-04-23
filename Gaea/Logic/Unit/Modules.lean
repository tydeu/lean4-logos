import Gaea.Logic.Logic
import Gaea.Logic.Unit.Rules
import Gaea.Logic.Unit.Theorems
import Gaea.Logic.Prop.Syntax

universe u
variable {P : Sort u}

namespace Gaea.Logic

variable {L : Logic P}

--------------------------------------------------------------------------------
-- Entailment 
--------------------------------------------------------------------------------

class LEnt (L : Logic P) extends LArr P :=
  Condition : Condition L toFun
  ModusPonens : ModusPonens L toFun

instance iLEnt {L : Logic P} [larr : LArr P] 
  [C : Condition L larr.toFun] [Mp : ModusPonens L larr.toFun] : LEnt L := 
  {toLArr := larr, Condition := C, ModusPonens := Mp}

namespace LEnt

abbrev funType (K : LEnt L) := Binar P
instance : CoeFun (LEnt L) funType := {coe := fun K => K.toFun}

instance [K : LEnt L] : 
  Logic.Condition L K.toFun := K.Condition
instance [K : LEnt L] : 
  Logic.ModusPonens L K.toFun := K.ModusPonens

-- Basic
abbrev condition (K : LEnt L) 
  {p q} := K.Condition.toFun p q
abbrev intro (K : LEnt L) 
  {p q} := K.Condition.toFun p q
abbrev elim (K : LEnt L) 
  {p q} := K.ModusPonens.toFun p q
abbrev mp (K : LEnt L) 
  {p q} := K.ModusPonens.toFun p q

-- Derived
abbrev Refl (K : LEnt L) 
  : Refl L K.toFun := iReflOfLeftCond
abbrev refl (K : LEnt L) 
  := K.Refl.toFun
abbrev rfl (K : LEnt L) 
  {p} := K.Refl.toFun p
abbrev Taut (K : LEnt L) 
  : Taut L K.toFun := iTautOfRefl
abbrev taut (K : LEnt L) 
  {p} := K.Taut.toFun p
abbrev RightTaut (K : LEnt L) 
  : RightTaut L K.toFun := iRightTautOfLeftCond
abbrev rightTaut (K : LEnt L) 
  {p q} := K.RightTaut.toFun p q
abbrev Trans (K : LEnt L) 
  : Trans L K.toFun := iTransByCondMp
abbrev trans (K : LEnt L) 
  {p q r} := K.Trans.toFun p q r

end LEnt

--------------------------------------------------------------------------------
-- Logical Biconditional (Iff)
--------------------------------------------------------------------------------

class LIff (L : Logic P) extends SIff P :=
  Bicondition : Bicondition L toFun
  LeftMp : LeftMp L toFun
  RightMp : RightMp L toFun

instance iLIff {L : Logic P} 
  [iff : SIff P] [B : Bicondition L iff.toFun] 
  [Mpl : LeftMp L iff.toFun] [Mpr : RightMp L iff.toFun] : LIff L := 
  {toSIff := iff, Bicondition := B, LeftMp := Mpl, RightMp := Mpr}

namespace LIff

abbrev funType (K : LIff L) := Binar P
instance : CoeFun (LIff L) funType := {coe := fun K => K.toFun}

instance [K : LIff L] :
  Logic.Bicondition L K.toFun := K.Bicondition
instance [K : LIff L] :
  Logic.LeftMp L K.toFun := K.LeftMp
instance [K : LIff L] :
  Logic.RightMp L K.toFun := K.RightMp

-- Basic
abbrev intro (K : LIff L) 
  {p q} := K.Bicondition.toFun p q
abbrev leftMp (K : LIff L) 
  {p q} := K.LeftMp.toFun p q
abbrev mp (K : LIff L) 
  {p q} := K.LeftMp.toFun p q
abbrev rightMp (K : LIff L) 
  {p q} := K.RightMp.toFun p q
abbrev mpr (K : LIff L) 
  {p q} := K.RightMp.toFun p q

-- Derived
abbrev Refl (K : LIff L) 
  : Refl L K.toFun := iReflOfBicondition
abbrev refl (K : LIff L) 
  := K.Refl.toFun
abbrev rfl (K : LIff L) 
  {p} := K.Refl.toFun p

end LIff

--------------------------------------------------------------------------------
-- Conjunction
--------------------------------------------------------------------------------

class LConj (L : Logic P) extends Conj P :=
  Conjoin : Conjoin L toFun
  LeftSimp : LeftSimp L toFun
  RightSimp : RightSimp L toFun
  Curry : Curry L toFun
  Uncurry : Uncurry L toFun

instance iLConjOfCurryUncurry {L : Logic P} [Cj : Conj P] 
  [CjC : Curry L Cj.toFun] [CjU : Uncurry L Cj.toFun] : LConj L := 
  {toConj := Cj, Curry := CjC, Uncurry := CjU, Conjoin := iConjoinOfCurry, 
    LeftSimp := iLeftSimpOfUncurry, RightSimp := iRightSimpOfUncurry}

instance iLConjOfLeftRightSimp 
  {L : Logic P} [Cj : Conj P] [Cjn : Conjoin L Cj.toFun] 
  [CjL : LeftSimp L Cj.toFun] [CjR : RightSimp L Cj.toFun] : LConj L := 
  {toConj := Cj, Conjoin := Cjn, LeftSimp := CjL, RightSimp := CjR,
    Curry := iCurryOfConjoin, Uncurry := iUncurryOfLeftRightSimp}

namespace LConj

instance [K : LConj L] :
  Logic.Conjoin L K.toFun := K.Conjoin
instance [K : LConj L] :
  Logic.LeftSimp L K.toFun := K.LeftSimp
instance [K : LConj L] :
  Logic.RightSimp L K.toFun := K.RightSimp

-- Basic
abbrev intro (K : LConj L) 
  {p q} := K.Conjoin.toFun p q
abbrev leftSimp (K : LConj L)
  {p q} := K.LeftSimp.toFun p q
abbrev left (K : LConj L)
  {p q} := K.LeftSimp.toFun p q
abbrev rightSimp (K : LConj L) 
  {p q} := K.RightSimp.toFun p q
abbrev right (K : LConj L) 
  {p q} := K.RightSimp.toFun p q
abbrev curry (K : LConj L) 
  {p q} := K.Curry.toFun p q
abbrev uncurry (K : LConj L) 
  {p q} := K.Uncurry.toFun p q

-- Derived
abbrev Taut (K : LConj L)
  : Taut L K.toFun := iTautOfConjoin
abbrev taut (K : LConj L)
  {p} := K.Taut.toFun p
abbrev Simp (K : LConj L)
  : Simp L K.toFun := iSimpOfLeft
abbrev simp (K : LConj L) 
  {p} := K.Simp.toFun p

end LConj

--------------------------------------------------------------------------------
-- Alternation
--------------------------------------------------------------------------------

class LAlt (L : Logic P) extends Disj P :=
  ByEither : ByEither L toFun
  LeftTaut : LeftTaut L toFun
  RightTaut : RightTaut L toFun

instance iLAlt {L : Logic P} [Dj : Disj P] 
  [E : ByEither L Dj.toFun] [IL : LeftTaut L Dj.toFun] [IR : RightTaut L Dj.toFun]  
  : LAlt L := {toDisj := Dj, ByEither := E, LeftTaut := IL, RightTaut := IR}

namespace LAlt

abbrev funType (K : LAlt L) := Binar P
instance : CoeFun (LAlt L) funType := {coe := fun K => K.toFun}

instance [K : LAlt L] :
  Logic.LeftTaut L K.toFun := K.LeftTaut
instance [K : LAlt L] :
  Logic.RightTaut L K.toFun := K.RightTaut
instance [K : LAlt L] :
  Logic.ByEither L K.toFun := K.ByEither

-- Basic
abbrev leftTaut (K : LAlt L)
  {p q} := K.LeftTaut.toFun p q
abbrev inl (K : LAlt L)
  {p q} := K.LeftTaut.toFun p q
abbrev rightTaut (K : LAlt L) 
  {p q} := K.RightTaut.toFun p q
abbrev inr (K : LAlt L) 
  {p q} := K.RightTaut.toFun p q
abbrev byEither (K : LAlt L) 
  {a p q} := K.ByEither.toFun a p q
abbrev elim (K : LAlt L) 
  {a p q} := K.ByEither.toFun a p q

-- Derived
abbrev Taut (K : LAlt L)
  : Taut L K.toFun := iTautOfLeft
abbrev taut (K : LAlt L)
  {p} := K.Taut.toFun p
abbrev Simp (K : LAlt L)
  : Simp L K.toFun := iSimpOfByEither
abbrev simp (K : LAlt L) 
  {p} := K.Simp.toFun p

end LAlt
