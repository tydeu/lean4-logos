import Logos.Logic.Logic
import Logos.Logic.Unit.Rules
import Logos.Logic.Unit.Theorems
import Logos.Logic.Prop.Syntax

universe u
variable {P : Sort u}

namespace Logos

variable {L : Logic P}

--------------------------------------------------------------------------------
-- Entailment 
--------------------------------------------------------------------------------

class LEnt (L : Logic P) extends LArr P :=
  Condition : Condition L larr
  ModusPonens : ModusPonens L larr

instance iLEnt {L : Logic P} [larr : LArr P] 
  [C : Condition L larr.toFun] [Mp : ModusPonens L larr.toFun] : LEnt L := 
  {toLArr := larr, Condition := C, ModusPonens := Mp}

namespace LEnt

instance [K : LEnt L] : 
  Logos.Condition L K.toFun := K.Condition
instance [K : LEnt L] : 
  Logos.ModusPonens L K.toFun := K.ModusPonens

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
  Bicondition : Bicondition L iff
  LeftMp : LeftMp L iff
  RightMp : RightMp L iff

instance iLIff {L : Logic P} 
  [iff : SIff P] [B : Bicondition L iff.1] 
  [Mpl : LeftMp L iff.1] [Mpr : RightMp L iff.1] : LIff L := 
  {toSIff := iff, Bicondition := B, LeftMp := Mpl, RightMp := Mpr}

namespace LIff

instance [K : LIff L] :
  Logos.Bicondition L K.toFun := K.Bicondition
instance [K : LIff L] :
  Logos.LeftMp L K.toFun := K.LeftMp
instance [K : LIff L] :
  Logos.RightMp L K.toFun := K.RightMp

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
  Conjoin : Conjoin L conj
  LeftSimp : LeftSimp L conj
  RightSimp : RightSimp L conj
  Curry : Curry L conj
  Uncurry : Uncurry L conj

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
  Logos.Conjoin L K.toFun := K.Conjoin
instance [K : LConj L] :
  Logos.LeftSimp L K.toFun := K.LeftSimp
instance [K : LConj L] :
  Logos.RightSimp L K.toFun := K.RightSimp

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
  ByEither : ByEither L disj
  LeftTaut : LeftTaut L disj
  RightTaut : RightTaut L disj

instance iLAlt {L : Logic P} [Dj : Disj P] 
  [E : ByEither L Dj.toFun] [IL : LeftTaut L Dj.toFun] [IR : RightTaut L Dj.toFun]  
  : LAlt L := {toDisj := Dj, ByEither := E, LeftTaut := IL, RightTaut := IR}

namespace LAlt

instance [K : LAlt L] :
  Logos.LeftTaut L K.toFun := K.LeftTaut
instance [K : LAlt L] :
  Logos.RightTaut L K.toFun := K.RightTaut
instance [K : LAlt L] :
  Logos.ByEither L K.toFun := K.ByEither

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
  {p q} (Fpq) {r} := K.ByEither.toFun p q Fpq r
abbrev elim (K : LAlt L) 
  {p q} (Fpq) {r} := K.ByEither.toFun p q Fpq r

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
