import Logos.Logic.Unit.Modules
import Logos.Logic.Quant.Modules
import Logos.Peano.Forall.Rules

universes u v
variable {P : Sort u} {T : Sort v}

namespace Logos.Peano

--------------------------------------------------------------------------------
-- Abstract Module
--------------------------------------------------------------------------------

class LForallNat (L : Logic P) (N : SNat P T) extends SForallNat P T :=
  ForallNatIntro : ForallNatIntro L N toSForallNat
  ForallNatElim : ForallNatElim L N toSForallNat

instance iLForallNat {L : Logic P} [N : SNat P T]
  [FaN : SForallNat P T] [I : ForallNatIntro L N FaN] [E : ForallNatElim L N FaN] 
  : LForallNat L N := {toSForallNat := FaN, ForallNatIntro := I, ForallNatElim := E}

namespace LForallNat

variable {L : Logic P} [N : SNat P T]
abbrev funType (K : LForallNat L N) := Quant P T
instance : CoeFun (LForallNat L N) funType := {coe := fun K => K.toFun}

instance [K : LForallNat L N] 
  : Peano.ForallNatIntro L N K.toSForallNat := K.ForallNatIntro
instance [K : LForallNat L N] 
  : Peano.ForallNatElim L N K.toSForallNat := K.ForallNatElim

abbrev intro (K : LForallNat L N) 
  {f} := K.ForallNatIntro.toFun f
abbrev elim (K : LForallNat L N) 
  {f} (p) {a} := K.ForallNatElim.toFun f p a

end LForallNat

--------------------------------------------------------------------------------
-- Forall/Ent Implementation Module
--------------------------------------------------------------------------------

def MForallIfNat {L : Logic P} 
  (N : SNat P T) (Fa : LForall L T) (ent : LEnt L) 
  : LForallNat L N := {
    toSForallNat := LForallIfNat N Fa.toSForall ent.toLArr, 
    ForallNatIntro := LForallIfNatIntro N Fa.UnivGen ent.Condition,
    ForallNatElim := LForallIfNatElim N Fa.UnivInst ent.ModusPonens,
  }

instance iMForallIfNat {P : Sort u} {T : Sort v} {L : Logic P} 
  [N : SNat P T] [Fa : LForall L T] [ent : LEnt L] : LForallNat L N
  := MForallIfNat N Fa ent
