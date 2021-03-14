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

instance {P : Sort u} {T : Sort v} {L : Logic P} {C : MForall L T} :
  ForallIntro L C.toLForall := {forallIntro := C.toForallIntro.forallIntro}

instance {P : Sort u} {T : Sort v} {L : Logic P} {C : MForall L T} :
  ForallElim L C.toLForall := {forallElim := C.toForallElim.forallElim}

namespace MForall
def forallIntro {P : Sort u} {T : Sort v} {L : Logic P} (C : MForall L T) 
  := C.toForallIntro.forallIntro
def ForallElim {P : Sort u} {T : Sort v} {L : Logic P} (C : MForall L T) 
  := C.toForallElim.forallElim
end MForall

-- If

class MIf {P : Sort u} (L : Logic P) extends LIf P :=
  (toIfIntro : IfIntro L toLIf)
  (toIfElim : IfElim L toLIf)

instance {P : Sort u} {L : Logic P} {C : MIf L} :
  IfIntro L C.toLIf := {ifIntro := C.toIfIntro.ifIntro}

instance {P : Sort u} {L : Logic P} {C : MIf L} :
  IfElim L C.toLIf := {ifElim := C.toIfElim.ifElim}

namespace MIf
def ifIntro {P : Sort u} {L : Logic P} {C : MIf L} 
  := C.toIfIntro.ifIntro
def ifElim {P : Sort u} {L : Logic P} {C : MIf L} 
  := C.toIfElim.ifElim
end MIf

end Gaea.Logic