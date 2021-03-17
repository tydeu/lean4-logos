import Gaea.Peano.Nat
import Gaea.Peano.Rules

universes u v w

open Gaea.Logic
open Gaea.Syntax

namespace Gaea.Peano

class PAdd {P : Sort u} {T : Type v} 
  (L : Logic P) (N : PNat P T) (Q : LEq P T) extends Add T :=
  (toAddNatZeroEqNat : AddNatZeroEqNat L N.toIsNat Q toAdd N.toZero)
  (toAddNatSuccEqSucc : AddNatSuccEqSucc  L N.toIsNat Q toAdd N.toSucc)

instance {P : Sort u} {T : Type v} {L : Logic P} 
  [N : PNat P T] [Q : LEq P T] [A : Add T] 
  [QZ : AddNatZeroEqNat L N.toIsNat Q A N.toZero] 
  [QS : AddNatSuccEqSucc L N.toIsNat Q A N.toSucc]
  : PAdd L N Q 
  := {toAdd := A, toAddNatZeroEqNat := QZ, toAddNatSuccEqSucc := QS}
 
instance {P : Sort u} {T : Type v} {L : Logic P} [N : PNat P T] [Q : LEq P T] 
  [A : PAdd L N Q] : AddNatZeroEqNat L N.toIsNat Q A.toAdd N.toZero := 
  {addNatZeroEqNat := A.toAddNatZeroEqNat.addNatZeroEqNat}

instance {P : Sort u} {T : Type v} {L : Logic P} [N : PNat P T] [Q : LEq P T] 
  [A : PAdd L N Q] : AddNatSuccEqSucc L N.toIsNat Q A.toAdd N.toSucc := 
  {addNatSuccEqSucc := A.toAddNatSuccEqSucc.addNatSuccEqSucc}

namespace PAdd
abbrev addNatZeroEqNat {P : Sort u} {T : Type v} 
  {L : Logic P} {N : PNat P T} {Q : LEq P T} (A : PAdd L N Q) 
  := A.toAddNatZeroEqNat.addNatZeroEqNat
abbrev addNatSuccEqSucc {P : Sort u} {T : Type v} 
  {L : Logic P} [N : PNat P T] [Q : LEq P T] (A : PAdd L N Q)
  := A.toAddNatSuccEqSucc.addNatSuccEqSucc
end PAdd

end Gaea.Peano