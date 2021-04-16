import Gaea.Logic.Logic
import Gaea.Logic.Prop.Rules
import Gaea.Logic.Prop.Theorems

universe u
variable {P : Sort u}

namespace Gaea.Logic

variable {L : Logic P}

--------------------------------------------------------------------------------
-- Implication
--------------------------------------------------------------------------------

class LImp (L : Logic P) extends Imp P :=
  Condition : Condition L toFun
  ModusPonens : ModusPonens L toFun

instance iLImp {L : Logic P} [imp : Imp P] 
  [ByI : Condition L imp.toFun] [Mp : ModusPonens L imp.toFun] : LImp L := 
  {toImp := imp, Condition := ByI, ModusPonens := Mp}

namespace LImp

abbrev funType (K : LImp L) := Binar P
instance : CoeFun (LImp L) funType := {coe := fun K => K.toFun}

instance [K : LImp L] : 
  Logic.Condition L K.toFun := K.Condition
instance [K : LImp L] : 
  Logic.ModusPonens L K.toFun := K.ModusPonens

-- Basic
abbrev condition (K : LImp L) 
  {p q} := K.Condition.condition p q
abbrev intro (K : LImp L) 
  {p q} := K.Condition.condition p q
abbrev elim (K : LImp L) 
  {p q} := K.ModusPonens.mp p q
abbrev mp (K : LImp L) 
  {p q} := K.ModusPonens.mp p q

-- Derived
abbrev Refl (K : LImp L) 
  : Refl L K.toFun := iImpReflByImp
abbrev refl (K : LImp L) 
  := K.Refl.refl
abbrev rfl (K : LImp L) 
  {p} := K.Refl.refl p
abbrev Taut (K : LImp L) 
  : Taut L K.toFun := iTautOfRefl
abbrev taut (K : LImp L) 
  {p} := K.Taut.taut p
abbrev RightTaut (K : LImp L) 
  : RightTaut L K.toFun := iImpRightTautByImp
abbrev rightTaut (K : LImp L) 
  {p q} := K.RightTaut.rightTaut p q
abbrev Trans (K : LImp L) 
  : Trans L K.toFun := iImpTransByImp
abbrev trans (K : LImp L) 
  {p q r} := K.Trans.trans p q r

end LImp

--------------------------------------------------------------------------------
-- Iff
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
  {p q} := K.Bicondition.bicondition p q
abbrev leftMp (K : LIff L) 
  {p q} := K.LeftMp.mp p q
abbrev mp (K : LIff L) 
  {p q} := K.LeftMp.mp p q
abbrev rightMp (K : LIff L) 
  {p q} := K.RightMp.mp p q
abbrev mpr (K : LIff L) 
  {p q} := K.RightMp.mp p q

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
  {p q} := K.Conjoin.conjoin p q
abbrev leftSimp (K : LConj L)
  {p q} := K.LeftSimp.leftSimp p q
abbrev left (K : LConj L)
  {p q} := K.LeftSimp.leftSimp p q
abbrev rightSimp (K : LConj L) 
  {p q} := K.RightSimp.rightSimp p q
abbrev right (K : LConj L) 
  {p q} := K.RightSimp.rightSimp p q
abbrev curry (K : LConj L) 
  {p q} := K.Curry.curry p q
abbrev uncurry (K : LConj L) 
  {p q} := K.Uncurry.uncurry p q

-- Derived
abbrev Taut (K : LConj L)
  : Taut L K.toFun := iTautOfConjoin
abbrev taut (K : LConj L)
  {p} := K.Taut.taut p
abbrev Simp (K : LConj L)
  : Simp L K.toFun := iSimpOfLeft
abbrev simp (K : LConj L) 
  {p} := K.Simp.simp p

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

abbrev funType (K : LSum L) := Binar P
instance : CoeFun (LSum L) funType := {coe := fun K => K.toFun}

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

class LDisj (L : Logic P) (lneg : Unar P) extends LSum L :=
  LeftMtp : LeftMtp L toFun lneg
  RightMtp : RightMtp L toFun lneg

instance iLDisj {L : Logic P} [Dj: Disj P] {lneg}
  [ByE : ByEither L Dj.toFun]  [LT : LeftTaut L Dj.toFun] [RT : RightTaut L Dj.toFun] 
  [LMtp : LeftMtp L Dj.toFun lneg] [RMtp : RightMtp L Dj.toFun lneg] 
  : LDisj L lneg := 
  {toDisj := Dj, ByEither := ByE, 
    LeftTaut := LT, RightTaut := RT, LeftMtp := LMtp, RightMtp := RMtp}

namespace LDisj

abbrev funType {lneg} (K : LDisj L lneg) := Binar P
instance {lneg} : CoeFun (LDisj L lneg) funType := {coe := fun K => K.toFun}

instance {lneg} [K : LDisj L lneg] :
  Logic.LeftMtp L K.toFun lneg := K.LeftMtp
instance {lneg} [K : LDisj L lneg] :
  Logic.RightMtp L K.toFun lneg := K.RightMtp

-- Basic
abbrev leftMtp {lneg} (K : LDisj L lneg)
  {p q} := K.LeftMtp.mtp p q
abbrev mtp {lneg} (K : LDisj L lneg)
  {p q} := K.LeftMtp.mtp p q
abbrev rightMtp {lneg} (K : LDisj L lneg)
  {p q} := K.RightMtp.mtp p q
abbrev mtpr {lneg} (K : LDisj L lneg)
  {p q} := K.RightMtp.mtp p q

end LDisj

--------------------------------------------------------------------------------
-- Not
--------------------------------------------------------------------------------

class LNot (L : Logic P) extends LNeg P :=
  AdFalso : AdFalso L toFun
  Noncontradiction : Noncontradiction L toFun

instance iLNot {L : Logic P} [Nt : LNeg P] 
  [Af : AdFalso L Nt.toFun] [Nc : Noncontradiction L Nt.toFun] : LNot L := 
  {toLNeg := Nt, AdFalso := Af, Noncontradiction := Nc}

namespace LNot

abbrev funType (K : LNot L) := Unar P
instance : CoeFun (LNot L) funType := {coe := fun K => K.toFun}

instance [K : LNot L] : 
  Logic.AdFalso L K.toFun := K.AdFalso
instance [K : LNot L] : 
  Logic.Noncontradiction L K.toFun := K.Noncontradiction

-- Basic
abbrev adFalso (K : LNot L) 
  {p} := K.AdFalso.adFalso p
abbrev intro (K : LNot L) 
  {p} := K.AdFalso.adFalso p
abbrev noncontradiction (K : LNot L) 
  {p} := K.Noncontradiction.noncontradiction p
abbrev elim (K : LNot L) 
  {p} := K.Noncontradiction.noncontradiction p

end LNot

end Gaea.Logic