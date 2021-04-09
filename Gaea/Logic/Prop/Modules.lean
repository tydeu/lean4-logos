import Gaea.Logic.Logic
import Gaea.Logic.Prop.Rules

universes u v
variable {P : Sort u} {T : Sort v}

namespace Gaea.Logic

-- Implication

class MImp (L : Logic P) extends Imp P :=
  (toImpByAssumption : ByAssumption L toImp.imp)
  (toImpModusPonens : ModusPonens L toImp.imp)

instance iMImp {L : Logic P} 
  [Imp : Imp P] [ByA : ByAssumption L Imp.imp] [Mp : ModusPonens L Imp.imp] :
  MImp L := {toImp := Imp, toImpByAssumption := ByA, toImpModusPonens := Mp}

namespace MImp
abbrev imp {L : Logic P} (K : MImp L) 
  := K.toImp.imp
abbrev toByAssumption {L : Logic P} (K : MImp L) 
  := K.toImpByAssumption
abbrev impIntro {L : Logic P} (K : MImp L) 
  := K.toImpByAssumption.byAssumption
abbrev intro {L : Logic P} (K : MImp L) 
  {p q} := K.impIntro p q
abbrev byAssumption {L : Logic P} (K : MImp L) 
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

instance iByAssumptionOfMImp {L : Logic P} {K : MImp L} :
  ByAssumption L K.imp := K.toImpByAssumption

instance iModusPonensOfMImp {L : Logic P} {K : MImp L} :
  ModusPonens L K.imp := K.toImpModusPonens

-- Iff

class MIff (L : Logic P) (Imp : Imp P) extends LIff P :=
  (toIffIntro : IffIntro L toLIff Imp)
  (toIffForw : IffForw L toLIff Imp)
  (toIffBack : IffBack L toLIff Imp)

instance iMIff {L : Logic P} [Iff : LIff P]
  [Imp : Imp P] [I : IffIntro L Iff Imp] [T : IffForw L Iff Imp] [F : IffBack L Iff Imp] :
  MIff L Imp := {toLIff := Iff, toIffIntro := I, toIffForw := T, toIffBack := F}

instance iIffIntroOfMIff {L : Logic P} [Imp : Imp P] [K : MIff L Imp] :
  IffIntro L K.toLIff Imp := K.toIffIntro

instance iIffForwOfMIff {L : Logic P} [Imp : Imp P] [K : MIff L Imp] :
  IffForw L K.toLIff Imp := K.toIffForw

instance iIffBackOfMIff {L : Logic P} [Imp : Imp P] [K : MIff L Imp] :
  IffBack L K.toLIff Imp := K.toIffBack

namespace MIff
abbrev iff {L : Logic P} {Imp : Imp P} (K : MIff L Imp) 
  := K.toLIff.iff
abbrev iffIntro {L : Logic P} {Imp : Imp P} (K : MIff L Imp) 
  := K.toIffIntro.iffIntro
abbrev intro {L : Logic P} {Imp : Imp P} (K : MIff L Imp) 
  {p q} := K.iffIntro p q
abbrev iffForw {L : Logic P} {Imp : Imp P} (K : MIff L Imp) 
  := K.toIffForw.iffForw
abbrev forw {L : Logic P} {Imp : Imp P} (K : MIff L Imp) 
  {p q} := K.iffForw p q
abbrev iffBack {L : Logic P} {Imp : Imp P} (K : MIff L Imp) 
  := K.toIffBack.iffBack
abbrev back {L : Logic P} {Imp : Imp P} (K : MIff L Imp) 
  {p q} := K.iffBack p q
end MIff

-- Conjunction

class MConj (L : Logic P) extends Conj P :=
  (toConjIntro : ConjIntro L toConj)
  (toConjLeft : ConjLeft L toConj)
  (toConjRight : ConjRight L toConj)

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
  (toDisjIntroLeft : DisjIntroLeft L toDisj)
  (toDisjIntroRight : DisjIntroRight L toDisj)
  (toDisjElim : DisjElim L toDisj)

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
  (toNotIntro : NotIntro L toLNot)
  (toNotElim : NotElim L toLNot)

instance iMNot {L : Logic P} 
  [Nt : LNot P] [I : NotIntro L Nt] [E : NotElim L Nt] : 
  MNot L := {toLNot := Nt, toNotIntro := I, toNotElim := E}

instance iNotIntroOfMNot {L : Logic P} [F : LFalse P] [K : MNot L] : 
  NotIntro L K.toLNot := K.toNotIntro

instance iNotElimOfMNot {L : Logic P} [F : LFalse P] [K : MNot L] : 
  NotElim L K.toLNot := K.toNotElim

namespace MNot
abbrev not {L : Logic P} (K : MNot L) 
  := K.toLNot.not
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