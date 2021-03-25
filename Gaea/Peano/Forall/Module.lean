import Gaea.Peano.Forall.Rules
import Gaea.Logic.Basic.Modules

universes u v

open Gaea.Logic

namespace Gaea.Peano

--------------------------------------------------------------------------------
-- Abstract Module
--------------------------------------------------------------------------------

class MForallNat {P : Sort u} {T : Sort v} 
  (L : Logic P) (N : IsNat P T) extends ForallNat P T :=
  (toForallNatIntro : ForallNatIntro L N toForallNat)
  (toForallNatElim : ForallNatElim L N toForallNat)

instance {P : Sort u} {T : Sort v} {L : Logic P} [N : IsNat P T]
  [FaN : ForallNat P T] [I : ForallNatIntro L N FaN] [E : ForallNatElim L N FaN] 
  : MForallNat L N := {toForallNat := FaN, toForallNatIntro := I, toForallNatElim := E}

instance {P : Sort u} {T : Sort v} {L : Logic P} [N : IsNat P T] 
  [K : MForallNat L N] : ForallNatIntro L N K.toForallNat 
  := {forallNatIntro := K.toForallNatIntro.forallNatIntro}

instance {P : Sort u} {T : Sort v} {L : Logic P} [N : IsNat P T] 
  [K : MForallNat L N] : ForallNatElim L N K.toForallNat 
  := {forallNatElim := K.toForallNatElim.forallNatElim}

namespace MForallNat
abbrev forallNatIntro {P : Sort u} {T : Sort v} {L : Logic P} {N : IsNat P T} 
  (K : MForallNat L N) := K.toForallNatIntro.forallNatIntro
abbrev ForallNatElim {P : Sort u} {T : Sort v} {L : Logic P} {N : IsNat P T} 
  (K : MForallNat L N) := K.toForallNatElim.forallNatElim
end MForallNat

--------------------------------------------------------------------------------
-- Forall/If Implementation Module
--------------------------------------------------------------------------------

def MForallIfNat {P : Sort u} {T : Type v} {L : Logic P} 
  (N : IsNat P T) (Fa : MForall L T) (If : MIf L) 
  : MForallNat L N := {
    toForallNat := LForallIfNat N Fa.toLForall If.toLIf, 
    toForallNatIntro := LForallIfNatIntro L N Fa.toLForall If.toLIf 
      Fa.toForallIntro If.toIfIntro,
    toForallNatElim := LForallIfNatElim L N Fa.toLForall If.toLIf 
      Fa.toForallElim If.toIfElim,
  }

instance iMForallIfNat {P : Sort u} {T : Type v} {L : Logic P} 
  [N : IsNat P T] [Fa : MForall L T] [If : MIf L] : MForallNat L N
  := MForallIfNat N Fa If

end Gaea.Peano