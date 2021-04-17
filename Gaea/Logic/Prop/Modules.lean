import Gaea.Logic.Logic
import Gaea.Logic.Prop.Rules
import Gaea.Logic.Prop.Theorems

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
  {p q} := K.Condition.condition p q
abbrev intro (K : LEnt L) 
  {p q} := K.Condition.condition p q
abbrev elim (K : LEnt L) 
  {p q} := K.ModusPonens.mp p q
abbrev mp (K : LEnt L) 
  {p q} := K.ModusPonens.mp p q

-- Derived
abbrev Refl (K : LEnt L) 
  : Refl L K.toFun := iImpReflByImp
abbrev refl (K : LEnt L) 
  := K.Refl.refl
abbrev rfl (K : LEnt L) 
  {p} := K.Refl.refl p
abbrev Taut (K : LEnt L) 
  : Taut L K.toFun := iTautOfRefl
abbrev taut (K : LEnt L) 
  {p} := K.Taut.taut p
abbrev RightTaut (K : LEnt L) 
  : RightTaut L K.toFun := iImpRightTautByImp
abbrev rightTaut (K : LEnt L) 
  {p q} := K.RightTaut.rightTaut p q
abbrev Trans (K : LEnt L) 
  : Trans L K.toFun := iImpTransByImp
abbrev trans (K : LEnt L) 
  {p q r} := K.Trans.trans p q r

end LEnt

--------------------------------------------------------------------------------
-- Implication 
--------------------------------------------------------------------------------

class LImp (L : Logic P) (lneg : Unar P) extends LEnt L :=
  ByContraposition : ByContraposition L toFun lneg
  ModusTollens : ModusTollens L toFun lneg

instance iLImp {L : Logic P} [larr : LArr P] {lneg : Unar P} 
  [C : Condition L larr.toFun] [Mp : ModusPonens L larr.toFun] 
  [ByC : ByContraposition L larr.toFun lneg] [Mt : ModusTollens L larr.toFun lneg] 
  : LImp L lneg := 
  {toLArr := larr, Condition := C, ModusPonens := Mp, 
    ByContraposition := ByC, ModusTollens := Mt}

namespace LImp

variable {lneg : Unar P}
abbrev funType (K : LImp L lneg) := Binar P
instance : CoeFun (LImp L lneg) funType := {coe := fun K => K.toFun}

instance [K : LImp L lneg] : 
  Logic.ModusTollens L K.toFun lneg := K.ModusTollens

-- Basic
abbrev mt (K : LImp L lneg) 
  {p q} := K.ModusTollens.mt p q

end LImp

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
-- Material Biconditional (Iff)
--------------------------------------------------------------------------------

class MIff (L : Logic P) (lneg : Unar P) extends LIff L :=
  LeftMt : LeftMt L toFun lneg
  RightMt : RightMt L toFun lneg

instance iMIff {L : Logic P} {lneg : Unar P}
  [iff : SIff P] [B : Bicondition L iff.toFun] 
  [Mpl : LeftMp L iff.toFun] [Mpr : RightMp L iff.toFun]
  [Mtl : LeftMt L iff.toFun lneg] [Mtr : RightMt L iff.toFun lneg] 
  : MIff L lneg := 
  {toSIff := iff, Bicondition := B, LeftMp := Mpl, RightMp := Mpr, 
    LeftMt := Mtl, RightMt := Mtr}

namespace MIff

variable {lneg : Unar P}
abbrev funType (K : MIff L lneg) := Binar P
instance : CoeFun (MIff L lneg) funType := {coe := fun K => K.toFun}

instance [K : MIff L lneg] :
  Logic.LeftMt L K.toFun lneg := K.LeftMt
instance [K : MIff L lneg] :
  Logic.RightMt L K.toFun lneg := K.RightMt

-- Basic
abbrev intro (K : MIff L lneg) 
  {p q} := K.Bicondition.bicondition p q
abbrev leftMt (K : MIff L lneg) 
  {p q} := K.LeftMt.mt p q
abbrev mt (K : MIff L lneg) 
  {p q} := K.LeftMt.mt p q
abbrev rightMt (K : MIff L lneg) 
  {p q} := K.RightMt.mt p q
abbrev mtr (K : MIff L lneg) 
  {p q} := K.RightMt.mt p q

end MIff

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
  {p q} := K.LeftTaut.leftTaut p q
abbrev inl (K : LAlt L)
  {p q} := K.LeftTaut.leftTaut p q
abbrev rightTaut (K : LAlt L) 
  {p q} := K.RightTaut.rightTaut p q
abbrev inr (K : LAlt L) 
  {p q} := K.RightTaut.rightTaut p q
abbrev byEither (K : LAlt L) 
  {a p q} := K.ByEither.byEither a p q
abbrev elim (K : LAlt L) 
  {a p q} := K.ByEither.byEither a p q

-- Derived
abbrev Taut (K : LAlt L)
  : Taut L K.toFun := iTautOfLeft
abbrev taut (K : LAlt L)
  {p} := K.Taut.taut p
abbrev Simp (K : LAlt L)
  : Simp L K.toFun := iSimpOfByEither
abbrev simp (K : LAlt L) 
  {p} := K.Simp.simp p

end LAlt

--------------------------------------------------------------------------------
-- Disjunction
--------------------------------------------------------------------------------

class LDisj (L : Logic P) (lneg : Unar P) extends LAlt L :=
  LeftMtp : LeftMtp L toFun lneg
  RightMtp : RightMtp L toFun lneg

instance iLDisj {L : Logic P} [Dj: Disj P] {lneg}
  [ByE : ByEither L Dj.toFun]  [LT : LeftTaut L Dj.toFun] [RT : RightTaut L Dj.toFun] 
  [LMtp : LeftMtp L Dj.toFun lneg] [RMtp : RightMtp L Dj.toFun lneg] 
  : LDisj L lneg := 
  {toDisj := Dj, ByEither := ByE, 
    LeftTaut := LT, RightTaut := RT, LeftMtp := LMtp, RightMtp := RMtp}

namespace LDisj

variable {lneg : Unar P}
abbrev funType (K : LDisj L lneg) := Binar P
instance : CoeFun (LDisj L lneg) funType := {coe := fun K => K.toFun}

instance [K : LDisj L lneg] :
  Logic.LeftMtp L K.toFun lneg := K.LeftMtp
instance [K : LDisj L lneg] :
  Logic.RightMtp L K.toFun lneg := K.RightMtp

-- Basic
abbrev leftMtp (K : LDisj L lneg)
  {p q} := K.LeftMtp.mtp p q
abbrev mtp (K : LDisj L lneg)
  {p q} := K.LeftMtp.mtp p q
abbrev rightMtp (K : LDisj L lneg)
  {p q} := K.RightMtp.mtp p q
abbrev mtpr (K : LDisj L lneg)
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