import Gaea.Logic.Basic
import Gaea.Logic.Rules
import Gaea.Syntax.Logic
import Gaea.Logic.Notation
import Gaea.Syntax.Notation

universes u v

open Gaea.Syntax

namespace Gaea.Logic

-- Forall

class MForall {P : Sort u} (L : Logic P) (T : Sort v) extends LForall P T :=
  (toForallIntro : ForallIntro L toLForall)
  (toForallElim : ForallElim L toLForall)

instance {P : Sort u} {T : Sort v} {L : Logic P} 
  [Fa : LForall P T] [I : ForallIntro L Fa] [E : ForallElim L Fa] :
  MForall L T := {toLForall := Fa, toForallIntro := I, toForallElim := E}

instance {P : Sort u} {T : Sort v} {L : Logic P} [C : MForall L T] :
  ForallIntro L C.toLForall := {forallIntro := C.toForallIntro.forallIntro}

instance {P : Sort u} {T : Sort v} {L : Logic P} [C : MForall L T] :
  ForallElim L C.toLForall := {forallElim := C.toForallElim.forallElim}

namespace MForall
def forallIntro {P : Sort u} {T : Sort v} {L : Logic P} (C : MForall L T) 
  := C.toForallIntro.forallIntro
def ForallElim {P : Sort u} {T : Sort v} {L : Logic P} (C : MForall L T) 
  := C.toForallElim.forallElim
end MForall

-- Exists

class MExists {P : Sort u} (L : Logic P) (T : Sort v) extends LExists P T :=
  (toExistsIntro : ExistsIntro L toLExists)
  (toExistsElim : ExistsElim L toLExists)

instance {P : Sort u} {T : Sort v} {L : Logic P} 
  [Fa : LExists P T] [I : ExistsIntro L Fa] [E : ExistsElim L Fa] :
  MExists L T := {toLExists := Fa, toExistsIntro := I, toExistsElim := E}

instance {P : Sort u} {T : Sort v} {L : Logic P} [C : MExists L T] :
  ExistsIntro L C.toLExists := {existsIntro := C.toExistsIntro.existsIntro}

instance {P : Sort u} {T : Sort v} {L : Logic P} [C : MExists L T] :
  ExistsElim L C.toLExists := {existsElim := C.toExistsElim.existsElim}

namespace MExists
def existsIntro {P : Sort u} {T : Sort v} {L : Logic P} (C : MExists L T) 
  := C.toExistsIntro.existsIntro
def ExistsElim {P : Sort u} {T : Sort v} {L : Logic P} (C : MExists L T) 
  := C.toExistsElim.existsElim
end MExists

-- If

class MIf {P : Sort u} (L : Logic P) extends LIf P :=
  (toIfIntro : IfIntro L toLIf)
  (toIfElim : IfElim L toLIf)

instance {P : Sort u} {T : Sort v} {L : Logic P} 
  [If : LIf P] [I : IfIntro L If] [E : IfElim L If] :
  MIf L := {toLIf := If, toIfIntro := I, toIfElim := E}

instance {P : Sort u} {L : Logic P} {C : MIf L} :
  IfIntro L C.toLIf := {ifIntro := C.toIfIntro.ifIntro}

instance {P : Sort u} {L : Logic P} {C : MIf L} :
  IfElim L C.toLIf := {ifElim := C.toIfElim.ifElim}

namespace MIf
def ifIntro {P : Sort u} {L : Logic P} (C : MIf L) 
  := C.toIfIntro.ifIntro
def ifElim {P : Sort u} {L : Logic P} (C : MIf L) 
  := C.toIfElim.ifElim
end MIf

-- Iff

class MIff {P : Sort u} (L : Logic P) (If : LIf P) extends LIff P :=
  (toIffIntro : IffIntro L toLIff If)
  (toIffTo : IffTo L toLIff If)
  (toIffFrom : IffFrom L toLIff If)

instance {P : Sort u} {T : Sort v} {L : Logic P} [Iff : LIff P]
  [If : LIf P] [I : IffIntro L Iff If] [T : IffTo L Iff If] [F : IffFrom L Iff If] :
  MIff L If := {toLIff := Iff, toIffIntro := I, toIffTo := T, toIffFrom := F}

instance {P : Sort u} {L : Logic P} [If : LIf P] [C : MIff L If] :
  IffIntro L C.toLIff If := {iffIntro := C.toIffIntro.iffIntro}

instance {P : Sort u} {L : Logic P} [If : LIf P] [C : MIff L If] :
  IffTo L C.toLIff If := {iffTo := C.toIffTo.iffTo}

instance {P : Sort u} {L : Logic P} [If : LIf P] [C : MIff L If] :
  IffFrom L C.toLIff If := {iffFrom := C.toIffFrom.iffFrom}

namespace MIff
def iffIntro {P : Sort u} {L : Logic P} {If : LIf P} (C : MIff L If) 
  := C.toIffIntro.iffIntro
def IffTo {P : Sort u} {L : Logic P} {If : LIf P} (C : MIff L If) 
  := C.toIffTo.iffTo
def IffFrom {P : Sort u} {L : Logic P} {If : LIf P} (C : MIff L If) 
  := C.toIffFrom.iffFrom
end MIff

-- And

class MAnd {P : Sort u} (L : Logic P) extends LAnd P :=
  (toAndIntro : AndIntro L toLAnd)
  (toAndLeft : AndLeft L toLAnd)
  (toAndRight : AndRight L toLAnd)

instance {P : Sort u} {T : Sort v} {L : Logic P} 
  [And : LAnd P] [I : AndIntro L And] [Lt : AndLeft L And] [Rt : AndRight L And] :
  MAnd L := {toLAnd := And, toAndIntro := I, toAndLeft := Lt, toAndRight := Rt}

instance {P : Sort u} {L : Logic P} [C : MAnd L] :
  AndIntro L C.toLAnd := {andIntro := C.toAndIntro.andIntro}

instance {P : Sort u} {L : Logic P} [C : MAnd L] :
  AndLeft L C.toLAnd := {andLeft := C.toAndLeft.andLeft}

instance {P : Sort u} {L : Logic P} [C : MAnd L] :
  AndRight L C.toLAnd := {andRight := C.toAndRight.andRight}

namespace MAnd
def andIntro {P : Sort u} {L : Logic P} (C : MAnd L) 
  := C.toAndIntro.andIntro
def andLeft {P : Sort u} {L : Logic P} (C : MAnd L)
  := C.toAndLeft.andLeft
def andRight {P : Sort u} {L : Logic P} (C : MAnd L) 
  := C.toAndRight.andRight
end MAnd

-- Not

class MNot {P : Sort u} (L : Logic P) 
  (If : LIf P) (F : LFalse P) extends LNot P :=
  (toNotIntro : NotIntro L toLNot If F)
  (toNotElim : NotElim L toLNot If F)

instance {P : Sort u} {T : Sort v} {L : Logic P} [Not : LNot P] 
  [If : LIf P] [F : LFalse P] [I : NotIntro L Not If F] [E : NotElim L Not If F] :
  MNot L If F := {toLNot := Not, toNotIntro := I, toNotElim := E}

instance {P : Sort u} {L : Logic P} 
  [If : LIf P] [F : LFalse P] [C : MNot L If F] :
  NotIntro L C.toLNot If F := {notIntro := C.toNotIntro.notIntro}

instance {P : Sort u} {L : Logic P}  
  [If : LIf P] [F : LFalse P] [C : MNot L If F] :
  NotElim L C.toLNot If F := {notElim := C.toNotElim.notElim}

namespace MNot
def notIntro {P : Sort u} {L : Logic P} 
  {If : LIf P} {F : LFalse P} (C : MNot L If F) 
  := C.toNotIntro.notIntro
def notElim {P : Sort u} {L : Logic P} 
  {If : LIf P} {F : LFalse P} (C : MNot L If F) 
  := C.toNotElim.notElim
end MNot

end Gaea.Logic