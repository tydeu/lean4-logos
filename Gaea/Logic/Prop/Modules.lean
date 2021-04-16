import Gaea.Logic.Logic
import Gaea.Logic.Prop.Rules

universe u
variable {P : Sort u}

namespace Gaea.Logic

variable {L : Logic P}

--------------------------------------------------------------------------------
-- Implication
--------------------------------------------------------------------------------

class MImp (L : Logic P) extends Imp P :=
  Condition : Condition L toFun
  ModusPonens : ModusPonens L toFun

instance iMImp {L : Logic P} 
  [Imp : Imp P] [ByI : Condition L Imp.toFun] [Mp : ModusPonens L Imp.toFun] :
  MImp L := {toImp := Imp, Condition := ByI, ModusPonens := Mp}

namespace MImp

instance [K : MImp L] : 
  Logic.Condition L K.toFun := K.Condition
instance [K : MImp L] : 
  Logic.ModusPonens L K.toFun := K.ModusPonens

-- Basic
abbrev condition (K : MImp L) 
  {p q} := K.Condition.condition p q
abbrev intro (K : MImp L) 
  {p q} := K.Condition.condition p q
abbrev elim (K : MImp L) 
  {p q} := K.ModusPonens.mp p q
abbrev mp (K : MImp L) 
  {p q} := K.ModusPonens.mp p q

end MImp

--------------------------------------------------------------------------------
-- Iff
--------------------------------------------------------------------------------

class MIff (L : Logic P) extends LIff P :=
  Bicondition : Bicondition L toFun
  LeftMp : LeftMp L toFun
  RightMp : RightMp L toFun

instance iMIff {L : Logic P} 
  [Iff : LIff P] [B : Bicondition L Iff.toFun] 
  [Mpl : LeftMp L Iff.toFun] [Mpr : RightMp L Iff.toFun] : MIff L := 
  {toLIff := Iff, Bicondition := B, LeftMp := Mpl, RightMp := Mpr}

namespace MIff

variable {L : Logic P}

instance [K : MIff L] :
  Logic.Bicondition L K.toFun := K.Bicondition
instance [K : MIff L] :
  Logic.LeftMp L K.toFun := K.LeftMp
instance [K : MIff L] :
  Logic.RightMp L K.toFun := K.RightMp

-- Basic
abbrev intro (K : MIff L) 
  {p q} := K.Bicondition.bicondition p q
abbrev leftMp (K : MIff L) 
  {p q} := K.LeftMp.mp p q
abbrev mp (K : MIff L) 
  {p q} := K.LeftMp.mp p q
abbrev rightMp (K : MIff L) 
  {p q} := K.RightMp.mp p q
abbrev mpr (K : MIff L) 
  {p q} := K.RightMp.mp p q

end MIff

--------------------------------------------------------------------------------
-- Conjunction
--------------------------------------------------------------------------------

class LConj (L : Logic P) extends Conj P :=
  Conjunction : Conjunction L toFun
  LeftSimp : LeftSimp L toFun
  RightSimp : RightSimp L toFun

instance iLConj {L : Logic P} 
  [Cj : Conj P] [CjI : Conjunction L Cj.toFun] 
  [CjL : LeftSimp L Cj.toFun] [CjR : RightSimp L Cj.toFun] : LConj L := 
  {toConj := Cj, Conjunction := CjI, LeftSimp := CjL, RightSimp := CjR}

namespace LConj

instance [K : LConj L] :
  Logic.Conjunction L K.toFun := K.Conjunction
instance [K : LConj L] :
  Logic.LeftSimp L K.toFun := K.LeftSimp
instance [K : LConj L] :
  Logic.RightSimp L K.toFun := K.RightSimp

-- Basic
abbrev intro (K : LConj L) 
  {p q} := K.Conjunction.conjoin p q
abbrev leftSimp (K : LConj L)
  {p q} := K.LeftSimp.leftSimp p q
abbrev left (K : LConj L)
  {p q} := K.LeftSimp.leftSimp p q
abbrev rightSimp (K : LConj L) 
  {p q} := K.RightSimp.rightSimp p q
abbrev right (K : LConj L) 
  {p q} := K.RightSimp.rightSimp p q

-- Derived
abbrev Taut (K : LConj L)
  : Taut L K.toFun := iTautOfConjunction
abbrev taut (K : LConj L)
  {p} := K.Taut.taut p
abbrev Simp (K : LConj L)
  : Simp L K.toFun := iSimpOfLeft
abbrev simp (K : LConj L) 
  {p} := K.Simp.simp p
abbrev Curry (K : LConj L)
  : Curry L K.toFun := iCurryOfConjunction
abbrev curry (K : LConj L) 
  {p q} := K.Curry.curry p q
abbrev Uncurry (K : LConj L)
  : Uncurry L K.toFun := iUncurryOfLeftRightSimp
abbrev uncurry (K : LConj L) 
  {p q} := K.Uncurry.uncurry p q

end LConj

--------------------------------------------------------------------------------
-- Disjunction
--------------------------------------------------------------------------------

class LSum (L : Logic P) extends Disj P :=
  ByEither : ByEither L toFun
  LeftTaut : LeftTaut L toFun
  RightTaut : RightTaut L toFun

instance iLSum {L : Logic P} [Dj : Disj P] 
  [E : ByEither L Dj.toFun] [IL : LeftTaut L Dj.toFun] [IR : RightTaut L Dj.toFun]  
  : LSum L := {toDisj := Dj, ByEither := E, LeftTaut := IL, RightTaut := IR}

namespace LSum

instance [K : LSum L] :
  Logic.LeftTaut L K.toFun := K.LeftTaut
instance [K : LSum L] :
  Logic.RightTaut L K.toFun := K.RightTaut
instance [K : LSum L] :
  Logic.ByEither L K.toFun := K.ByEither

-- Basic
abbrev leftTaut (K : LSum L)
  {p q} := K.LeftTaut.leftTaut p q
abbrev inl (K : LSum L)
  {p q} := K.LeftTaut.leftTaut p q
abbrev rightTaut (K : LSum L) 
  {p q} := K.RightTaut.rightTaut p q
abbrev inr (K : LSum L) 
  {p q} := K.RightTaut.rightTaut p q
abbrev byEither (K : LSum L) 
  {a p q} := K.ByEither.byEither a p q
abbrev elim (K : LSum L) 
  {a p q} := K.ByEither.byEither a p q

-- Derived
abbrev Taut (K : LSum L)
  : Taut L K.toFun := iTautOfLeft
abbrev taut (K : LSum L)
  {p} := K.Taut.taut p
abbrev Simp (K : LSum L)
  : Simp L K.toFun := iSimpOfByEither
abbrev simp (K : LSum L) 
  {p} := K.Simp.simp p

end LSum

class LDisj (L : Logic P) (lnot : Unar P) extends LSum L :=
  LeftMtp : LeftMtp L toFun lnot
  RightMtp : RightMtp L toFun lnot

instance iLDisj {L : Logic P} [Dj: Disj P] {lnot}
  [ByE : ByEither L Dj.toFun]  [LT : LeftTaut L Dj.toFun] [RT : RightTaut L Dj.toFun] 
  [LMtp : LeftMtp L Dj.toFun lnot] [RMtp : RightMtp L Dj.toFun lnot] 
  : LDisj L lnot := 
  {toDisj := Dj, ByEither := ByE, 
    LeftTaut := LT, RightTaut := RT, LeftMtp := LMtp, RightMtp := RMtp}

namespace LDisj

instance {lnot} [K : LDisj L lnot] :
  Logic.LeftMtp L K.toFun lnot := K.LeftMtp
instance {lnot} [K : LDisj L lnot] :
  Logic.RightMtp L K.toFun lnot := K.RightMtp

-- Basic
abbrev leftMtp {lnot} (K : LDisj L lnot)
  {p q} := K.LeftMtp.mtp p q
abbrev mtp {lnot} (K : LDisj L lnot)
  {p q} := K.LeftMtp.mtp p q
abbrev rightMtp {lnot} (K : LDisj L lnot)
  {p q} := K.RightMtp.mtp p q
abbrev mtpr {lnot} (K : LDisj L lnot)
  {p q} := K.RightMtp.mtp p q

end LDisj

--------------------------------------------------------------------------------
-- Not
--------------------------------------------------------------------------------

class MNot (L : Logic P) extends LNot P :=
  AdFalso : AdFalso L toFun
  Noncontradiction : Noncontradiction L toFun

instance iMNot {L : Logic P} [Nt : LNot P] 
  [Af : AdFalso L Nt.toFun] [Nc : Noncontradiction L Nt.toFun] : MNot L := 
  {toLNot := Nt, AdFalso := Af, Noncontradiction := Nc}

namespace MNot

instance [K : MNot L] : 
  Logic.AdFalso L K.toFun := K.AdFalso
instance [K : MNot L] : 
  Logic.Noncontradiction L K.toFun := K.Noncontradiction

-- Basic
abbrev adFalso (K : MNot L) 
  {p} := K.AdFalso.adFalso p
abbrev intro (K : MNot L) 
  {p} := K.AdFalso.adFalso p
abbrev noncontradiction (K : MNot L) 
  {p} := K.Noncontradiction.noncontradiction p
abbrev elim (K : MNot L) 
  {p} := K.Noncontradiction.noncontradiction p

end MNot

end Gaea.Logic