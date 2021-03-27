import Gaea.Logic.Logic
import Gaea.Logic.Basic.Rules


namespace Gaea.Logic

universes u v
variable {P : Sort u} {T : Sort v}

-- Forall

class MForall (L : Logic P) (T : Sort v) extends LForall P T :=
  toForallIntro : ForallIntro L toLForall
  toForallElim : ForallElim L toLForall

instance iMForall {L : Logic P} 
  [Fa : LForall P T] [I : ForallIntro L Fa] [E : ForallElim L Fa] :
  MForall L T := {toLForall := Fa, toForallIntro := I, toForallElim := E}

instance iForallIntroOfMForall {L : Logic P} [K : MForall L T] :
  ForallIntro L K.toLForall := {forallIntro := K.toForallIntro.forallIntro}

instance iForallElimOfMForall {L : Logic P} [K : MForall L T] :
  ForallElim L K.toLForall := {forallElim := K.toForallElim.forallElim}

namespace MForall
abbrev lForall {L : Logic P} (K : MForall L T) 
  := K.toLForall.lForall
abbrev forallIntro {L : Logic P} (K : MForall L T) 
  := K.toForallIntro.forallIntro
abbrev intro {L : Logic P} (K : MForall L T) 
  {f} := K.forallIntro f
abbrev forallElim {L : Logic P} (K : MForall L T) 
  := K.toForallElim.forallElim
abbrev elim {L : Logic P} (K : MForall L T) 
  {f} := K.forallElim f
end MForall

-- Exists

class MExists (L : Logic P) (T : Sort v) extends LExists P T :=
  toExistsIntro : ExistsIntro L toLExists
  toExistsElim : ExistsElim L toLExists

instance iMExists {L : Logic P} 
  [Fa : LExists P T] [I : ExistsIntro L Fa] [E : ExistsElim L Fa] :
  MExists L T := {toLExists := Fa, toExistsIntro := I, toExistsElim := E}

instance iExistsIntroOfMExists {L : Logic P} [K : MExists L T] :
  ExistsIntro L K.toLExists := {existsIntro := K.toExistsIntro.existsIntro}

instance iExistsElimOfMExists {L : Logic P} [K : MExists L T] :
  ExistsElim L K.toLExists := {existsElim := K.toExistsElim.existsElim}

namespace MExists
abbrev lExists {L : Logic P} (K : MExists L T) 
  := K.toLExists.lExists 
abbrev existsIntro {L : Logic P} (K : MExists L T) 
  := K.toExistsIntro.existsIntro
abbrev intro {L : Logic P} (K : MExists L T) 
  {f} := K.existsIntro f
abbrev existsElim {L : Logic P} (K : MExists L T) 
  := K.toExistsElim.existsElim
abbrev elim {L : Logic P} (K : MExists L T) 
  {f} := K.existsElim f
end MExists

-- If

class MIf (L : Logic P) extends LIf P :=
  (toIfIntro : IfIntro L toLIf)
  (toIfElim : IfElim L toLIf)

instance iMIf {L : Logic P} 
  [If : LIf P] [I : IfIntro L If] [E : IfElim L If] :
  MIf L := {toLIf := If, toIfIntro := I, toIfElim := E}

instance iIfIntroOfMIf {L : Logic P} {K : MIf L} :
  IfIntro L K.toLIf := {ifIntro := K.toIfIntro.ifIntro}

instance iIfElimOfMIf {L : Logic P} {K : MIf L} :
  IfElim L K.toLIf := {ifElim := K.toIfElim.ifElim}

namespace MIf
abbrev lIf {L : Logic P} (K : MIf L) 
  := K.toLIf.lIf
abbrev ifIntro {L : Logic P} (K : MIf L) 
  := K.toIfIntro.ifIntro
abbrev intro {L : Logic P} (K : MIf L) 
  {p q} := K.ifIntro p q
abbrev ifElim {L : Logic P} (K : MIf L) 
  := K.toIfElim.ifElim
abbrev elim {L : Logic P} (K : MIf L) 
  {p q} := K.ifElim p q
end MIf

-- Iff

class MIff (L : Logic P) (If : LIf P) extends LIff P :=
  (toIffIntro : IffIntro L toLIff If)
  (toIffForw : IffForw L toLIff If)
  (toIffBack : IffBack L toLIff If)

instance iMIff {L : Logic P} [Iff : LIff P]
  [If : LIf P] [I : IffIntro L Iff If] [T : IffForw L Iff If] [F : IffBack L Iff If] :
  MIff L If := {toLIff := Iff, toIffIntro := I, toIffForw := T, toIffBack := F}

instance iIffIntroOfMIff {L : Logic P} [If : LIf P] [K : MIff L If] :
  IffIntro L K.toLIff If := {iffIntro := K.toIffIntro.iffIntro}

instance iIffForwOfMIff {L : Logic P} [If : LIf P] [K : MIff L If] :
  IffForw L K.toLIff If := {iffForw := K.toIffForw.iffForw}

instance iIffBackOfMIff {L : Logic P} [If : LIf P] [K : MIff L If] :
  IffBack L K.toLIff If := {iffBack := K.toIffBack.iffBack}

namespace MIff
abbrev lIff {L : Logic P} {If : LIf P} (K : MIff L If) 
  := K.toLIff.lIff
abbrev iffIntro {L : Logic P} {If : LIf P} (K : MIff L If) 
  := K.toIffIntro.iffIntro
abbrev intro {L : Logic P} {If : LIf P} (K : MIff L If) 
  {p q} := K.iffIntro p q
abbrev iffForw {L : Logic P} {If : LIf P} (K : MIff L If) 
  := K.toIffForw.iffForw
abbrev forw {L : Logic P} {If : LIf P} (K : MIff L If) 
  {p q} := K.iffForw p q
abbrev iffBack {L : Logic P} {If : LIf P} (K : MIff L If) 
  := K.toIffBack.iffBack
abbrev back {L : Logic P} {If : LIf P} (K : MIff L If) 
  {p q} := K.iffBack p q
end MIff

-- Conjunction

class MConj (L : Logic P) extends Conj P :=
  (toConjIntro : ConjIntro L toConj)
  (toConjLeft : ConjLeft L toConj)
  (toConjRight : ConjRight L toConj)

instance iMConj {L : Logic P} 
  [Cj : Conj P] [I : ConjIntro L Cj] [Lt : ConjLeft L Cj] [Rt : ConjRight L Cj] :
  MConj L := {toConj := Cj, toConjIntro := I, toConjLeft := Lt, toConjRight := Rt}

instance iConjIntroOfMConj {L : Logic P} [K : MConj L] :
  ConjIntro L K.toConj := {conjIntro := K.toConjIntro.conjIntro}

instance iConjLeftOfMConj {L : Logic P} [K : MConj L] :
  ConjLeft L K.toConj := {conjLeft := K.toConjLeft.conjLeft}

instance iConjRightOfMConj {L : Logic P} [K : MConj L] :
  ConjRight L K.toConj := {conjRight := K.toConjRight.conjRight}

namespace MConj
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
end MConj

-- Not

class MNot (L : Logic P) (F : LFalse P) extends LNot P :=
  (toNotIntro : NotIntro L toLNot F)
  (toNotElim : NotElim L toLNot F)

instance iMNot {L : Logic P} 
  [Nt : LNot P] [F : LFalse P] [I : NotIntro L Nt F] [E : NotElim L Nt F] :
  MNot L F := {toLNot := Nt, toNotIntro := I, toNotElim := E}

instance iNotIntroOfMNot {L : Logic P} [F : LFalse P] [K : MNot L F] :
  NotIntro L K.toLNot F := {notIntro := K.toNotIntro.notIntro}

instance iNotElimOfMNot {L : Logic P} [F : LFalse P] [K : MNot L F] :
  NotElim L K.toLNot F := {notElim := K.toNotElim.notElim}

namespace MNot
abbrev lNot {L : Logic P} {F : LFalse P} (K : MNot L F) 
  := K.toLNot.lNot
abbrev notIntro {L : Logic P} {F : LFalse P} (K : MNot L F) 
  := K.toNotIntro.notIntro
abbrev intro {L : Logic P} {F : LFalse P} (K : MNot L F) 
  {p} := K.notIntro p
abbrev notElim {L : Logic P} {F : LFalse P} (K : MNot L F) 
  := K.toNotElim.notElim
abbrev elim {L : Logic P} {F : LFalse P} (K : MNot L F) 
  {p} := K.notElim p
end MNot

end Gaea.Logic