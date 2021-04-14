import Gaea.Logic.Logic
import Gaea.Logic.Prop.Rules

universes u v
variable {P : Sort u} {T : Sort v}

namespace Gaea.Logic

--------------------------------------------------------------------------------
-- Implication
--------------------------------------------------------------------------------

class MImp (L : Logic P) extends Imp P :=
  toImpByImplication : ByImplication L toImp.imp
  toImpModusPonens : ModusPonens L toImp.imp

instance iMImp {L : Logic P} 
  [Imp : Imp P] [ByI : ByImplication L Imp.imp] [Mp : ModusPonens L Imp.imp] :
  MImp L := {toImp := Imp, toImpByImplication := ByI, toImpModusPonens := Mp}

instance iByImplicationOfMImp {L : Logic P} {K : MImp L} :
  ByImplication L K.imp := K.toImpByImplication

instance iModusPonensOfMImp {L : Logic P} {K : MImp L} :
  ModusPonens L K.imp := K.toImpModusPonens

namespace MImp
abbrev toByImplication {L : Logic P} (K : MImp L) 
  := K.toImpByImplication
abbrev impIntro {L : Logic P} (K : MImp L) 
  := K.toImpByImplication.byImplication
abbrev intro {L : Logic P} (K : MImp L) 
  {p q} := K.impIntro p q
abbrev byImplication {L : Logic P} (K : MImp L) 
  {p q} := K.impIntro p q
abbrev toModusPonens {L : Logic P} (K : MImp L) 
  := K.toImpModusPonens
abbrev impElim {L : Logic P} (K : MImp L) 
  := K.toImpModusPonens.mp
abbrev elim {L : Logic P} (K : MImp L) 
  {p q} := K.impElim p q
abbrev mp {L : Logic P} (K : MImp L) 
  {p q} := K.impElim p q
end MImp

--------------------------------------------------------------------------------
-- Iff
--------------------------------------------------------------------------------

class MIff (L : Logic P) extends LIff P :=
  toIffBicondition : Bicondition L toLIff.iff
  toIffLeftMp : LeftMp L toLIff.iff
  toIffRightMp : RightMp L toLIff.iff

instance iMIff {L : Logic P} 
[Iff : LIff P] [B : Bicondition L Iff.iff] 
[Mpl : LeftMp L Iff.iff] [Mpr : RightMp L Iff.iff] 
: MIff L := 
{toLIff := Iff, 
  toIffBicondition := B,  toIffLeftMp := Mpl, toIffRightMp := Mpr}

instance iBiconditionOfMIff {L : Logic P} [K : MIff L] :
  Bicondition L K.iff := K.toIffBicondition

instance iLeftMpOfMIff {L : Logic P} [K : MIff L] :
  LeftMp L K.iff := K.toIffLeftMp

instance iRightMpOfMIff {L : Logic P} [K : MIff L] :
  RightMp L K.iff := K.toIffRightMp

namespace MIff
abbrev iffBicondition {L : Logic P} (K : MIff L) 
  := K.toIffBicondition.bicondition
abbrev intro {L : Logic P} (K : MIff L) 
  {p q} := K.iffBicondition p q
abbrev toLeftMp {L : Logic P} (K : MIff L) 
  := K.toIffLeftMp
abbrev iffLeftMp {L : Logic P} (K : MIff L) 
  := K.toIffLeftMp.mp
abbrev leftMp {L : Logic P} (K : MIff L) 
  {p q} := K.iffLeftMp p q
abbrev mp {L : Logic P} (K : MIff L) 
  {p q} := K.iffLeftMp p q
abbrev toRightMp {L : Logic P} (K : MIff L) 
  := K.toIffRightMp
abbrev iffRightMp {L : Logic P} (K : MIff L) 
  := K.toIffLeftMp.mp
abbrev rightMp {L : Logic P} (K : MIff L) 
  {p q} := K.iffRightMp p q
abbrev mpr {L : Logic P} (K : MIff L) 
  {p q} := K.iffRightMp p q
end MIff

--------------------------------------------------------------------------------
-- Conjunction
--------------------------------------------------------------------------------

class LConj (L : Logic P) extends Conj P :=
  toConjunction : Conjunction L toConj.conj
  toConjLeftSimp : LeftSimp L toConj.conj
  toConjRightSimp : RightSimp L toConj.conj

instance iLConj {L : Logic P} 
  [Cj : Conj P] [CjI : Conjunction L Cj.conj] 
  [CjL : LeftSimp L Cj.conj] [CjR : RightSimp L Cj.conj] 
  : LConj L := 
  {toConj := Cj, toConjunction := CjI, 
    toConjLeftSimp := CjL, toConjRightSimp := CjR}

instance iConjunctionOfLConj {L : Logic P} [K : LConj L] :
  Conjunction L K.conj := K.toConjunction

instance iLeftSimpOfLConj {L : Logic P} [K : LConj L] :
  LeftSimp L K.conj := K.toConjLeftSimp

instance iRightSimpOfLConj {L : Logic P} [K : LConj L] :
  RightSimp L K.conj := K.toConjRightSimp

namespace LConj

-- Basic
abbrev conjoin {L : Logic P} (K : LConj L) 
  := K.toConjunction.conjoin
abbrev intro {L : Logic P} (K : LConj L) 
  {p q} := K.conjoin p q
abbrev toLeftSimp {L : Logic P} (K : LConj L)
  := K.toConjLeftSimp
abbrev disjLeftSimp {L : Logic P} (K : LConj L)
  := K.toConjLeftSimp.leftSimp
abbrev leftSimp {L : Logic P} (K : LConj L)
  {p q} := K.disjLeftSimp p q
abbrev left {L : Logic P} (K : LConj L)
  {p q} := K.disjLeftSimp p q
abbrev toRightSimp {L : Logic P} (K : LConj L) 
  := K.toConjRightSimp
abbrev disjRightSimp {L : Logic P} (K : LConj L) 
  := K.toConjRightSimp.rightSimp
abbrev rightSimp {L : Logic P} (K : LConj L) 
  {p q} := K.disjRightSimp p q
abbrev right {L : Logic P} (K : LConj L) 
  {p q} := K.disjRightSimp p q

-- Derived
abbrev toTaut {L : Logic P} (K : LConj L)
  : Taut L K.conj := iTautOfConjunction
abbrev conjTaut {L : Logic P} (K : LConj L)
  := K.toTaut.taut
abbrev taut {L : Logic P} (K : LConj L)
  {p} := K.conjTaut p
abbrev toSimp {L : Logic P} (K : LConj L)
  : Simp L K.conj := iSimpOfLeft
abbrev conjSimp {L : Logic P} (K : LConj L) 
  := K.toSimp.simp
abbrev simp {L : Logic P} (K : LConj L) 
  {p} := K.conjSimp p
abbrev toCurry {L : Logic P} (K : LConj L)
  : Curry L K.conj := iCurryOfConjunction
abbrev conjCurry {L : Logic P} (K : LConj L) 
  := K.toCurry.curry
abbrev curry {L : Logic P} (K : LConj L) 
  {p q} := K.conjCurry p q
abbrev toUncurry {L : Logic P} (K : LConj L)
  : Uncurry L K.conj := iUncurryOfLeftRightSimp
abbrev conjUncurry {L : Logic P} (K : LConj L) 
  := K.toUncurry.uncurry
abbrev uncurry {L : Logic P} (K : LConj L) 
  {p q} := K.conjUncurry p q

end LConj

--------------------------------------------------------------------------------
-- Disjunction
--------------------------------------------------------------------------------

class LSum (L : Logic P) extends Disj P :=
  toDisjByEither : ByEither L toDisj.disj
  toDisjLeftTaut : LeftTaut L toDisj.disj
  toDisjRightTaut : RightTaut L toDisj.disj

instance iLSum {L : Logic P} [Dj : Disj P] 
  [IL : LeftTaut L Dj.disj] [IR : RightTaut L Dj.disj] [E : ByEither L Dj.disj] 
  : LSum L := 
  {toDisj := Dj, toDisjLeftTaut := IL, toDisjRightTaut := IR, toDisjByEither := E}

instance iLeftTautOfLSum {L : Logic P} [K : LSum L] :
  LeftTaut L K.disj := K.toDisjLeftTaut

instance iRightTautOfLSum {L : Logic P} [K : LSum L] :
  RightTaut L K.disj := K.toDisjRightTaut

instance iByEitherOfLSum {L : Logic P} [K : LSum L] :
  ByEither L K.disj := K.toDisjByEither

namespace LSum

-- Basic
abbrev toLeftTaut {L : Logic P} (K : LSum L)
  := K.toDisjLeftTaut
abbrev disjLeftTaut {L : Logic P} (K : LSum L)
  := K.toDisjLeftTaut.leftTaut
abbrev leftTaut {L : Logic P} (K : LSum L)
  {p q} := K.disjLeftTaut p q
abbrev inl {L : Logic P} (K : LSum L)
  {p q} := K.disjLeftTaut p q
abbrev toRightTaut {L : Logic P} (K : LSum L) 
  := K.toDisjRightTaut
abbrev disjRightTaut {L : Logic P} (K : LSum L) 
  := K.toDisjRightTaut.rightTaut
abbrev rightTaut {L : Logic P} (K : LSum L) 
  {p q} := K.disjRightTaut p q
abbrev inr {L : Logic P} (K : LSum L) 
  {p q} := K.disjRightTaut p q
abbrev toByEither {L : Logic P} (K : LSum L) 
  := K.toDisjByEither
abbrev disjByEither {L : Logic P} (K : LSum L) 
  := K.toDisjByEither.byEither
abbrev byEither {L : Logic P} (K : LSum L) 
  {a p q} := K.disjByEither a p q
abbrev elim {L : Logic P} (K : LSum L) 
  {a p q} := K.disjByEither a p q

-- Derived
abbrev toTaut {L : Logic P} (K : LSum L)
  : Taut L K.disj := iTautOfLeft
abbrev disjTaut {L : Logic P} (K : LSum L)
  := K.toTaut.taut
abbrev taut {L : Logic P} (K : LSum L)
  {p} := K.disjTaut p
abbrev toSimp {L : Logic P} (K : LSum L)
  : Simp L K.disj := iSimpOfByEither
abbrev disjSimp {L : Logic P} (K : LSum L) 
  := K.toSimp.simp
abbrev simp {L : Logic P} (K : LSum L) 
  {p} := K.disjSimp p

end LSum

class LDisj (L : Logic P) (lnot : Unar P) extends LSum L :=
  toDisjLeftMtp : LeftMtp L disj lnot
  toDisjRightMtp : RightMtp L disj lnot

instance iLDisj {L : Logic P} [Dj: Disj P] {lnot}
  [ByE : ByEither L Dj.disj]  [LT : LeftTaut L Dj.disj] [RT : RightTaut L Dj.disj] 
  [LMtp : LeftMtp L Dj.disj lnot] [RMtp : RightMtp L Dj.disj lnot] 
  : LDisj L lnot := 
  {toDisj := Dj, toDisjByEither := ByE, 
    toDisjLeftTaut := LT, toDisjRightTaut := RT, 
    toDisjLeftMtp := LMtp, toDisjRightMtp := RMtp}

instance iLeftMtpOfLDisj {L : Logic P} {lnot} [K : LDisj L lnot] :
  LeftMtp L K.disj lnot := K.toDisjLeftMtp

instance iRightMtpOfLDisj {L : Logic P} {lnot} [K : LDisj L lnot] :
  RightMtp L K.disj lnot := K.toDisjRightMtp

namespace LDisj
abbrev toLeftMtp {L : Logic P} {lnot} (K : LDisj L lnot)
  := K.toDisjLeftMtp
abbrev disjLeftMtp {L : Logic P} {lnot} (K : LDisj L lnot)
  := K.toDisjLeftMtp.mtp
abbrev leftMtp {L : Logic P} {lnot} (K : LDisj L lnot)
  {p q} := K.disjLeftMtp p q
abbrev mtp {L : Logic P} {lnot} (K : LDisj L lnot)
  {p q} := K.disjLeftMtp p q
abbrev toRightMtp {L : Logic P} {lnot} (K : LDisj L lnot) 
  := K.toDisjRightMtp
abbrev disjRightMtp {L : Logic P} {lnot} (K : LDisj L lnot) 
  := K.toDisjRightMtp.mtp
abbrev rightMtp {L : Logic P} {lnot} (K : LDisj L lnot)
  {p q} := K.disjRightMtp p q
abbrev mtpr {L : Logic P} {lnot} (K : LDisj L lnot)
  {p q} := K.disjRightMtp p q
end LDisj

--------------------------------------------------------------------------------
-- Not
--------------------------------------------------------------------------------

class MNot (L : Logic P) extends LNot P :=
  toNotAdFalso : AdFalso L toLNot.not
  toNotNoncontradiction : Noncontradiction L toLNot.not

instance iMNot {L : Logic P} 
  [Nt : LNot P] [Af : AdFalso L Nt.not] [Nc : Noncontradiction L Nt.not] : 
  MNot L := {toLNot := Nt, toNotAdFalso := Af, toNotNoncontradiction := Nc}

instance iAdFalsoOfMNot {L : Logic P} [F : LFalse P] [K : MNot L] : 
  AdFalso L K.not := K.toNotAdFalso

instance iNoncontradictionOfMNot {L : Logic P} [F : LFalse P] [K : MNot L] : 
  Noncontradiction L K.not := K.toNotNoncontradiction

namespace MNot
abbrev toAdFalso {L : Logic P} (K : MNot L) 
  := K.toNotAdFalso
abbrev notAdFalso {L : Logic P} (K : MNot L) 
  := K.toNotAdFalso.adFalso
abbrev adFalso {L : Logic P} (K : MNot L) 
  {p} := K.notAdFalso p
abbrev intro {L : Logic P} (K : MNot L) 
  {p} := K.notAdFalso p
abbrev toNoncontradiction {L : Logic P} (K : MNot L) 
  := K.toNotNoncontradiction
abbrev notNoncontradiction {L : Logic P} (K : MNot L) 
  := K.toNotNoncontradiction.noncontradiction
abbrev noncontradiction {L : Logic P} (K : MNot L) 
  {p} := K.notNoncontradiction p
abbrev elim {L : Logic P} (K : MNot L) 
  {p} := K.notNoncontradiction p
end MNot

end Gaea.Logic