import Gaea.Logic.Prop.Modules
import Gaea.Logic.Quant.Modules
import Gaea.Peano.Forall.Rules

open Gaea.Logic

universes u v
variable {P : Sort u} {T : Sort v}

namespace Gaea.Peano

--------------------------------------------------------------------------------
-- Abstract Module
--------------------------------------------------------------------------------

class MForallNat (L : Logic P) (N : IsNat P T) extends ForallNat P T :=
  (toForallNatIntro : ForallNatIntro L N toForallNat)
  (toForallNatElim : ForallNatElim L N toForallNat)

instance iMForallNat {L : Logic P} [N : IsNat P T]
  [FaN : ForallNat P T] [I : ForallNatIntro L N FaN] [E : ForallNatElim L N FaN] 
  : MForallNat L N := {toForallNat := FaN, toForallNatIntro := I, toForallNatElim := E}

instance iForallNatIntroOfMForallNat {L : Logic P} [N : IsNat P T] 
  [K : MForallNat L N] : ForallNatIntro L N K.toForallNat 
  := {forallNatIntro := K.toForallNatIntro.forallNatIntro}

instance iForallNatElimOfMForallNat {L : Logic P} [N : IsNat P T] 
  [K : MForallNat L N] : ForallNatElim L N K.toForallNat 
  := {forallNatElim := K.toForallNatElim.forallNatElim}

namespace MForallNat
abbrev forallNatIntro {L : Logic P} {N : IsNat P T} (K : MForallNat L N) 
  := K.toForallNatIntro.forallNatIntro
abbrev intro {L : Logic P} {N : IsNat P T} (K : MForallNat L N) 
  {f} := K.toForallNatIntro.forallNatIntro f
abbrev forallNatElim {L : Logic P} {N : IsNat P T} (K : MForallNat L N) 
  := K.toForallNatElim.forallNatElim
abbrev elim {L : Logic P} {N : IsNat P T} (K : MForallNat L N) 
  {f} (p) {a} := K.toForallNatElim.forallNatElim f p a
end MForallNat

--------------------------------------------------------------------------------
-- Forall/Imp Implementation Module
--------------------------------------------------------------------------------

def MForallIfNat {L : Logic P} 
  (N : IsNat P T) (Fa : MForall L T) (Im : MImp L) 
  : MForallNat L N := {
    toForallNat := LForallIfNat N Fa.toLForall Im.toImp, 
    toForallNatIntro := LForallIfNatIntro N Fa.toUnivGen Im.Condition,
    toForallNatElim := LForallIfNatElim N Fa.toUnivInst Im.ModusPonens,
  }

instance iMForallIfNat {P : Sort u} {T : Type v} {L : Logic P} 
  [N : IsNat P T] [Fa : MForall L T] [Im : MImp L] : MForallNat L N
  := MForallIfNat N Fa Im

end Gaea.Peano