import Gaea.Logic.Logic
import Gaea.Logic.Prop.Rules

universes u v
variable {P : Sort u} {T : Sort v}

namespace Gaea.Logic

-- Implication

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

-- Iff

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
  := K.toIffModusPonensRev.mpr
abbrev mpr {L : Logic P} (K : MIff L) 
  {p q} := K.iffMpr p q
end MIff

-- Conjunction

class MConj (L : Logic P) extends Conj P :=
  toConjIntro : ConjIntro L toConj
  toConjLeft : ConjLeft L toConj
  toConjRight : ConjRight L toConj

instance iMConj {L : Logic P} [Cj : Conj P] 
  [I : ConjIntro L Cj] [CjL : ConjLeft L Cj] [CjR : ConjRight L Cj] : MConj L 
  := {toConj := Cj, toConjIntro := I, toConjLeft := CjL, toConjRight := CjR}

instance iConjIntroOfMConj {L : Logic P} [K : MConj L] :
  ConjIntro L K.toConj := K.toConjIntro

instance iConjLeftOfMConj {L : Logic P} [K : MConj L] :
  ConjLeft L K.toConj := K.toConjLeft

instance iConjRightOfMConj {L : Logic P} [K : MConj L] :
  ConjRight L K.toConj := K.toConjRight

namespace MConj

-- Basic
abbrev conj {L : Logic P} (K : MConj L) 
  := K.toConj.conj
abbrev conjIntro {L : Logic P} (K : MConj L) 
  := K.toConjIntro.conjIntro
abbrev intro {L : Logic P} (K : MConj L) 
  {p q} := K.conjIntro p q
abbrev conjLeft {L : Logic P} (K : MConj L)
  := K.toConjLeft.conjLeft
abbrev left {L : Logic P} (K : MConj L)
  {p q} := K.conjLeft p q
abbrev conjRight {L : Logic P} (K : MConj L) 
  := K.toConjRight.conjRight
abbrev right {L : Logic P} (K : MConj L) 
  {p q} := K.conjRight p q

-- Derived
abbrev toConjTaut {L : Logic P} (K : MConj L)
  : ConjTaut L K.toConj := iConjTautOfIntro
abbrev conjTaut {L : Logic P} (K : MConj L)
  := K.toConjTaut.conjTaut
abbrev taut {L : Logic P} (K : MConj L)
  {p q} := K.conjTaut p q
abbrev toConjSimp {L : Logic P} (K : MConj L)
  : ConjSimp L K.toConj := iConjSimpOfLeft
abbrev conjSimp {L : Logic P} (K : MConj L) 
  := K.toConjSimp.conjSimp
abbrev simp {L : Logic P} (K : MConj L) 
  {p q} := K.conjSimp p q
abbrev toConjCurry {L : Logic P} (K : MConj L)
  : ConjCurry L K.toConj := iConjCurryOfIntro
abbrev conjCurry {L : Logic P} (K : MConj L) 
  := K.toConjCurry.conjCurry
abbrev curry {L : Logic P} (K : MConj L) 
  {p q} := K.conjCurry p q
abbrev toConjUncurry {L : Logic P} (K : MConj L)
  : ConjUncurry L K.toConj := iConjUncurryOfLeftRight
abbrev conjUncurry {L : Logic P} (K : MConj L) 
  := K.toConjUncurry.conjUncurry
abbrev uncurry {L : Logic P} (K : MConj L) 
  {p q} := K.conjUncurry p q

end MConj

-- Disjunction

class MDisj (L : Logic P) extends Disj P :=
  toDisjIntroLeft : DisjIntroLeft L toDisj
  toDisjIntroRight : DisjIntroRight L toDisj
  toDisjElim : DisjElim L toDisj

instance iMDisj {L : Logic P} [Dj : Disj P] 
  [IL : DisjIntroLeft L Dj] [IR : DisjIntroRight L Dj] [E : DisjElim L Dj] : MDisj L := 
  {toDisj := Dj, toDisjIntroLeft := IL, toDisjIntroRight := IR, toDisjElim := E}

instance iDisjIntroLeftOfMDisj {L : Logic P} [K : MDisj L] :
  DisjIntroLeft L K.toDisj := K.toDisjIntroLeft

instance iDisjIntroRightOfMDisj {L : Logic P} [K : MDisj L] :
  DisjIntroRight L K.toDisj := K.toDisjIntroRight

instance iDisjElimOfMDisj {L : Logic P} [K : MDisj L] :
  DisjElim L K.toDisj := K.toDisjElim

namespace MDisj

-- Basic
abbrev disj {L : Logic P} (K : MDisj L) 
  := K.toDisj.disj
abbrev disjIntroLeft {L : Logic P} (K : MDisj L)
  := K.toDisjIntroLeft.disjIntroLeft
abbrev inl {L : Logic P} (K : MDisj L)
  {p q} := K.disjIntroLeft p q
abbrev disjIntroRight {L : Logic P} (K : MDisj L) 
  := K.toDisjIntroRight.disjIntroRight
abbrev inr {L : Logic P} (K : MDisj L) 
  {p q} := K.disjIntroRight p q
abbrev disjElim {L : Logic P} (K : MDisj L) 
  := K.toDisjElim.disjElim
abbrev elim {L : Logic P} (K : MDisj L) 
  {a p q} := K.disjElim a p q

-- Derived
abbrev toDisjTaut {L : Logic P} (K : MDisj L)
  : DisjTaut L K.toDisj := iDisjTautOfIntroLeft
abbrev disjTaut {L : Logic P} (K : MDisj L)
  := K.toDisjTaut.disjTaut
abbrev taut {L : Logic P} (K : MDisj L)
  {p q} := K.disjTaut p q
abbrev toDisjSimp {L : Logic P} (K : MDisj L)
  : DisjSimp L K.toDisj := iDisjSimpOfElim
abbrev disjSimp {L : Logic P} (K : MDisj L) 
  := K.toDisjSimp.disjSimp
abbrev simp {L : Logic P} (K : MDisj L) 
  {p q} := K.disjSimp p q

end MDisj

-- Not

class MNot (L : Logic P) extends LNot P :=
  toNotIntro : NotIntro L toLNot.not
  toNotElim : NotElim L toLNot.not

instance iMNot {L : Logic P} 
  [Nt : LNot P] [I : NotIntro L Nt.not] [E : NotElim L Nt.not] : 
  MNot L := {toLNot := Nt, toNotIntro := I, toNotElim := E}

instance iNotIntroOfMNot {L : Logic P} [F : LFalse P] [K : MNot L] : 
  NotIntro L K.not := K.toNotIntro

instance iNotElimOfMNot {L : Logic P} [F : LFalse P] [K : MNot L] : 
  NotElim L K.not := K.toNotElim

namespace MNot
abbrev notIntro {L : Logic P} (K : MNot L) 
  := K.toNotIntro.notIntro
abbrev intro {L : Logic P} (K : MNot L) 
  {p} := K.notIntro p
abbrev notElim {L : Logic P} (K : MNot L) 
  := K.toNotElim.notElim
abbrev elim {L : Logic P} (K : MNot L) 
  {p} := K.notElim p
end MNot

end Gaea.Logic