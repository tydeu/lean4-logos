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
  toIffModusPonens : ModusPonens L toLIff.iff
  toIffModusPonensRev : ModusPonensRev L toLIff.iff

instance iMIff {L : Logic P} 
[Iff : LIff P] [B : Bicondition L Iff.iff] 
[Mp : ModusPonens L Iff.iff] [Mpr : ModusPonensRev L Iff.iff] 
: MIff L := 
{toLIff := Iff, 
  toIffBicondition := B,  toIffModusPonens := Mp, toIffModusPonensRev := Mpr}

instance iBiconditionOfMIff {L : Logic P} [K : MIff L] :
  Bicondition L K.iff := K.toIffBicondition

instance iIffForwOfMIff {L : Logic P} [K : MIff L] :
  ModusPonens L K.iff := K.toIffModusPonens

instance iIffBackOfMIff {L : Logic P} [K : MIff L] :
  ModusPonensRev L K.iff := K.toIffModusPonensRev

namespace MIff
abbrev iffBicondition {L : Logic P} (K : MIff L) 
  := K.toIffBicondition.bicondition
abbrev intro {L : Logic P} (K : MIff L) 
  {p q} := K.iffBicondition p q
abbrev iffMp {L : Logic P} (K : MIff L) 
  := K.toIffModusPonens.mp
abbrev mp {L : Logic P} (K : MIff L) 
  {p q} := K.iffMp p q
abbrev iffMpr {L : Logic P} (K : MIff L) 
  := K.toIffModusPonensRev.mp
abbrev mpr {L : Logic P} (K : MIff L) 
  {p q} := K.iffMpr p q
end MIff

--------------------------------------------------------------------------------
-- Conjunction
--------------------------------------------------------------------------------

class MConj (L : Logic P) extends Conj P :=
  toConjunction : Conjunction L toConj.conj
  toConjLeftSimp : LeftSimp L toConj.conj
  toConjRightSimp : RightSimp L toConj.conj

instance iMConj {L : Logic P} 
  [Cj : Conj P] [CjI : Conjunction L Cj.conj] 
  [CjL : LeftSimp L Cj.conj] [CjR : RightSimp L Cj.conj] 
  : MConj L := 
  {toConj := Cj, toConjunction := CjI, 
    toConjLeftSimp := CjL, toConjRightSimp := CjR}

instance iConjunctionOfMConj {L : Logic P} [K : MConj L] :
  Conjunction L K.conj := K.toConjunction

instance iLeftSimpOfMConj {L : Logic P} [K : MConj L] :
  LeftSimp L K.conj := K.toConjLeftSimp

instance iRightSimpOfMConj {L : Logic P} [K : MConj L] :
  RightSimp L K.conj := K.toConjRightSimp

namespace MConj

-- Basic
abbrev conjoin {L : Logic P} (K : MConj L) 
  := K.toConjunction.conjoin
abbrev intro {L : Logic P} (K : MConj L) 
  {p q} := K.conjoin p q
abbrev toLeftSimp {L : Logic P} (K : MConj L)
  := K.toConjLeftSimp
abbrev disjLeftSimp {L : Logic P} (K : MConj L)
  := K.toConjLeftSimp.leftSimp
abbrev leftSimp {L : Logic P} (K : MConj L)
  {p q} := K.disjLeftSimp p q
abbrev left {L : Logic P} (K : MConj L)
  {p q} := K.disjLeftSimp p q
abbrev toRightSimp {L : Logic P} (K : MConj L) 
  := K.toConjRightSimp
abbrev disjRightSimp {L : Logic P} (K : MConj L) 
  := K.toConjRightSimp.rightSimp
abbrev rightSimp {L : Logic P} (K : MConj L) 
  {p q} := K.disjRightSimp p q
abbrev right {L : Logic P} (K : MConj L) 
  {p q} := K.disjRightSimp p q

-- Derived
-- abbrev toTautology {L : Logic P} (K : MConj L)
--   : Tautology L K.conj := iTautOfConjunction
-- abbrev conjTaut {L : Logic P} (K : MConj L)
--   := K.toTautology.taut
-- abbrev taut {L : Logic P} (K : MConj L)
--   {p} := K.conjTaut p
abbrev toSimplification {L : Logic P} (K : MConj L)
  : Simplification L K.conj := iSimpOfLeft
abbrev conjSimp {L : Logic P} (K : MConj L) 
  := K.toSimplification.simp
abbrev simp {L : Logic P} (K : MConj L) 
  {p} := K.conjSimp p
abbrev toCurry {L : Logic P} (K : MConj L)
  : Curry L K.conj := iCurryOfConjunction
abbrev conjCurry {L : Logic P} (K : MConj L) 
  := K.toCurry.curry
abbrev curry {L : Logic P} (K : MConj L) 
  {p q} := K.conjCurry p q
abbrev toUncurry {L : Logic P} (K : MConj L)
  : Uncurry L K.conj := iUncurryOfLeftRightSimp
abbrev conjUncurry {L : Logic P} (K : MConj L) 
  := K.toUncurry.uncurry
abbrev uncurry {L : Logic P} (K : MConj L) 
  {p q} := K.conjUncurry p q

end MConj

-- Disjunction

class MDisj (L : Logic P) extends Disj P :=
  toDisjByEither : ByEither L toDisj.disj
  toDisjLeftTaut : LeftTaut L toDisj.disj
  toDisjRightTaut : RightTaut L toDisj.disj

instance iMDisj {L : Logic P} [Dj : Disj P] 
  [IL : LeftTaut L Dj.disj] [IR : RightTaut L Dj.disj] [E : ByEither L Dj.disj] 
  : MDisj L := 
  {toDisj := Dj, toDisjLeftTaut := IL, toDisjRightTaut := IR, toDisjByEither := E}

instance iLeftTautOfMDisj {L : Logic P} [K : MDisj L] :
  LeftTaut L K.disj := K.toDisjLeftTaut

instance iRightTautOfMDisj {L : Logic P} [K : MDisj L] :
  RightTaut L K.disj := K.toDisjRightTaut

instance iByEitherOfMDisj {L : Logic P} [K : MDisj L] :
  ByEither L K.disj := K.toDisjByEither

namespace MDisj

-- Basic
abbrev toLeftTaut {L : Logic P} (K : MDisj L)
  := K.toDisjLeftTaut
abbrev disjLeftTaut {L : Logic P} (K : MDisj L)
  := K.toDisjLeftTaut.leftTaut
abbrev leftTaut {L : Logic P} (K : MDisj L)
  {p q} := K.disjLeftTaut p q
abbrev inl {L : Logic P} (K : MDisj L)
  {p q} := K.disjLeftTaut p q
abbrev toRightTaut {L : Logic P} (K : MDisj L) 
  := K.toDisjRightTaut
abbrev disjRightTaut {L : Logic P} (K : MDisj L) 
  := K.toDisjRightTaut.rightTaut
abbrev rightTaut {L : Logic P} (K : MDisj L) 
  {p q} := K.disjRightTaut p q
abbrev inr {L : Logic P} (K : MDisj L) 
  {p q} := K.disjRightTaut p q
abbrev toByEither {L : Logic P} (K : MDisj L) 
  := K.toDisjByEither
abbrev disjByEither {L : Logic P} (K : MDisj L) 
  := K.toDisjByEither.byEither
abbrev byEither {L : Logic P} (K : MDisj L) 
  {a p q} := K.disjByEither a p q
abbrev elim {L : Logic P} (K : MDisj L) 
  {a p q} := K.disjByEither a p q

-- Derived
abbrev toTautology {L : Logic P} (K : MDisj L)
  : Tautology L K.disj := iTautOfLeft
abbrev disjTaut {L : Logic P} (K : MDisj L)
  := K.toTautology.taut
abbrev taut {L : Logic P} (K : MDisj L)
  {p} := K.disjTaut p
abbrev intro {L : Logic P} (K : MDisj L)
  {p q} := K.disjTaut p q
-- abbrev toSimplification {L : Logic P} (K : MDisj L)
--   : Simplification L K.disj := iSimpOfByEither
-- abbrev disjSimp {L : Logic P} (K : MDisj L) 
--   := K.toSimplification.simp
-- abbrev simp {L : Logic P} (K : MDisj L) 
--   {p} := K.disjSimp p

end MDisj

-- Not

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
abbrev nc {L : Logic P} (K : MNot L) 
  {p} := K.notNoncontradiction p
abbrev elim {L : Logic P} (K : MNot L) 
  {p} := K.notNoncontradiction p
end MNot

end Gaea.Logic