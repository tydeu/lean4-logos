import Gaea.Logic.Logic
import Gaea.Logic.Basic.Rules

universes u v

namespace Gaea.Logic

-- Forall

class MForall {P : Sort u} (L : Logic P) (T : Sort v) extends LForall P T :=
  (toForallIntro : ForallIntro L toLForall)
  (toForallElim : ForallElim L toLForall)

instance {P : Sort u} {T : Sort v} {L : Logic P} 
  [Fa : LForall P T] [I : ForallIntro L Fa] [E : ForallElim L Fa] :
  MForall L T := {toLForall := Fa, toForallIntro := I, toForallElim := E}

instance {P : Sort u} {T : Sort v} {L : Logic P} [K : MForall L T] :
  ForallIntro L K.toLForall := {forallIntro := K.toForallIntro.forallIntro}

instance {P : Sort u} {T : Sort v} {L : Logic P} [K : MForall L T] :
  ForallElim L K.toLForall := {forallElim := K.toForallElim.forallElim}

namespace MForall
abbrev forallIntro {P : Sort u} {T : Sort v} {L : Logic P} (K : MForall L T) 
  := K.toForallIntro.forallIntro
abbrev ForallElim {P : Sort u} {T : Sort v} {L : Logic P} (K : MForall L T) 
  := K.toForallElim.forallElim
end MForall

-- Exists

class MExists {P : Sort u} (L : Logic P) (T : Sort v) extends LExists P T :=
  (toExistsIntro : ExistsIntro L toLExists)
  (toExistsElim : ExistsElim L toLExists)

instance {P : Sort u} {T : Sort v} {L : Logic P} 
  [Fa : LExists P T] [I : ExistsIntro L Fa] [E : ExistsElim L Fa] :
  MExists L T := {toLExists := Fa, toExistsIntro := I, toExistsElim := E}

instance {P : Sort u} {T : Sort v} {L : Logic P} [K : MExists L T] :
  ExistsIntro L K.toLExists := {existsIntro := K.toExistsIntro.existsIntro}

instance {P : Sort u} {T : Sort v} {L : Logic P} [K : MExists L T] :
  ExistsElim L K.toLExists := {existsElim := K.toExistsElim.existsElim}

namespace MExists
abbrev existsIntro {P : Sort u} {T : Sort v} {L : Logic P} (K : MExists L T) 
  := K.toExistsIntro.existsIntro
abbrev ExistsElim {P : Sort u} {T : Sort v} {L : Logic P} (K : MExists L T) 
  := K.toExistsElim.existsElim
end MExists

-- If

class MIf {P : Sort u} (L : Logic P) extends LIf P :=
  (toIfIntro : IfIntro L toLIf)
  (toIfElim : IfElim L toLIf)

instance {P : Sort u} {T : Sort v} {L : Logic P} 
  [If : LIf P] [I : IfIntro L If] [E : IfElim L If] :
  MIf L := {toLIf := If, toIfIntro := I, toIfElim := E}

instance {P : Sort u} {L : Logic P} {K : MIf L} :
  IfIntro L K.toLIf := {ifIntro := K.toIfIntro.ifIntro}

instance {P : Sort u} {L : Logic P} {K : MIf L} :
  IfElim L K.toLIf := {ifElim := K.toIfElim.ifElim}

namespace MIf
abbrev ifIntro {P : Sort u} {L : Logic P} (K : MIf L) 
  := K.toIfIntro.ifIntro
abbrev ifElim {P : Sort u} {L : Logic P} (K : MIf L) 
  := K.toIfElim.ifElim
end MIf

-- Iff

class MIff {P : Sort u} (L : Logic P) (If : LIf P) extends LIff P :=
  (toIffIntro : IffIntro L toLIff If)
  (toIffTo : IffTo L toLIff If)
  (toIffFrom : IffFrom L toLIff If)

instance {P : Sort u} {T : Sort v} {L : Logic P} [Iff : LIff P]
  [If : LIf P] [I : IffIntro L Iff If] [T : IffTo L Iff If] [F : IffFrom L Iff If] :
  MIff L If := {toLIff := Iff, toIffIntro := I, toIffTo := T, toIffFrom := F}

instance {P : Sort u} {L : Logic P} [If : LIf P] [K : MIff L If] :
  IffIntro L K.toLIff If := {iffIntro := K.toIffIntro.iffIntro}

instance {P : Sort u} {L : Logic P} [If : LIf P] [K : MIff L If] :
  IffTo L K.toLIff If := {iffTo := K.toIffTo.iffTo}

instance {P : Sort u} {L : Logic P} [If : LIf P] [K : MIff L If] :
  IffFrom L K.toLIff If := {iffFrom := K.toIffFrom.iffFrom}

namespace MIff
abbrev iffIntro {P : Sort u} {L : Logic P} {If : LIf P} (K : MIff L If) 
  := K.toIffIntro.iffIntro
abbrev IffTo {P : Sort u} {L : Logic P} {If : LIf P} (K : MIff L If) 
  := K.toIffTo.iffTo
abbrev IffFrom {P : Sort u} {L : Logic P} {If : LIf P} (K : MIff L If) 
  := K.toIffFrom.iffFrom
end MIff

-- Conjunction

class MConj {P : Sort u} (L : Logic P) extends Conj P :=
  (toConjIntro : ConjIntro L toConj)
  (toConjLeft : ConjLeft L toConj)
  (toConjRight : ConjRight L toConj)

instance {P : Sort u} {T : Sort v} {L : Logic P} 
  [Cj : Conj P] [I : ConjIntro L Cj] [Lt : ConjLeft L Cj] [Rt : ConjRight L Cj] :
  MConj L := {toConj := Cj, toConjIntro := I, toConjLeft := Lt, toConjRight := Rt}

instance {P : Sort u} {L : Logic P} [K : MConj L] :
  ConjIntro L K.toConj := {conjIntro := K.toConjIntro.conjIntro}

instance {P : Sort u} {L : Logic P} [K : MConj L] :
  ConjLeft L K.toConj := {conjLeft := K.toConjLeft.conjLeft}

instance {P : Sort u} {L : Logic P} [K : MConj L] :
  ConjRight L K.toConj := {conjRight := K.toConjRight.conjRight}

namespace MConj
abbrev conjIntro {P : Sort u} {L : Logic P} (K : MConj L) 
  := K.toConjIntro.conjIntro
abbrev conjLeft {P : Sort u} {L : Logic P} (K : MConj L)
  := K.toConjLeft.conjLeft
abbrev conjRight {P : Sort u} {L : Logic P} (K : MConj L) 
  := K.toConjRight.conjRight
end MConj

-- Not

class MNot {P : Sort u} (L : Logic P) (F : LFalse P) extends LNot P :=
  (toNotIntro : NotIntro L toLNot F)
  (toNotElim : NotElim L toLNot F)

instance {P : Sort u} {T : Sort v} {L : Logic P} 
  [Nt : LNot P] [F : LFalse P] [I : NotIntro L Nt F] [E : NotElim L Nt F] :
  MNot L F := {toLNot := Nt, toNotIntro := I, toNotElim := E}

instance {P : Sort u} {L : Logic P} [F : LFalse P] [K : MNot L F] :
  NotIntro L K.toLNot F := {notIntro := K.toNotIntro.notIntro}

instance {P : Sort u} {L : Logic P} [F : LFalse P] [K : MNot L F] :
  NotElim L K.toLNot F := {notElim := K.toNotElim.notElim}

namespace MNot
abbrev notIntro {P : Sort u} {L : Logic P} {F : LFalse P} (K : MNot L F) 
  := K.toNotIntro.notIntro
abbrev notElim {P : Sort u} {L : Logic P} {F : LFalse P} (K : MNot L F) 
  := K.toNotElim.notElim
end MNot

end Gaea.Logic