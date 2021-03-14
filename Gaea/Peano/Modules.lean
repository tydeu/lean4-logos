import Gaea.Peano.Nat
import Gaea.Peano.Rules

universes u v w

open Gaea.Logic
open Gaea.Syntax

namespace Gaea.Peano

--------------------------------------------------------------------------------
-- Addition
--------------------------------------------------------------------------------

class PAdd {P : Sort u} {T : Type v} 
  (L : Logic P) (N : Nat P T) (Eq : LEq P T) extends Add T :=
  (toAddNatZeroEqNat : AddNatZeroEqNat L N.toIsNat Eq toAdd N.toZero)
  (toAddNatSuccEqSucc : AddNatSuccEqSucc  L N.toIsNat Eq toAdd N.toSucc)

instance {P : Sort u} {T : Type v} {L : Logic P} {N : Nat P T} {Eq : LEq P T} 
  {A : PAdd L N Eq} : AddNatZeroEqNat L N.toIsNat Eq A.toAdd N.toZero := 
  {addNatZeroEqNat := A.toAddNatZeroEqNat.addNatZeroEqNat}

instance {P : Sort u} {T : Type v} {L : Logic P} {N : Nat P T} {Eq : LEq P T} 
  {A : PAdd L N Eq} : AddNatSuccEqSucc L N.toIsNat Eq A.toAdd N.toSucc := 
  {addNatSuccEqSucc := A.toAddNatSuccEqSucc.addNatSuccEqSucc}

namespace PAdd
def addNatZeroEqNat {P : Sort u} {T : Type v} 
  {L : Logic P} {N : Nat P T} {Eq : LEq P T} (A : PAdd L N Eq) 
  := A.toAddNatZeroEqNat.addNatZeroEqNat
def An0_eq_n {P : Sort u} {T : Type v} 
  {L : Logic P} [N : Nat P T] [Eq : LEq P T] (A : PAdd L N Eq) 
  {a : T} := A.toAddNatZeroEqNat.addNatZeroEqNat a
def addNatSuccEqSucc {P : Sort u} {T : Type v} 
  {L : Logic P} [N : Nat P T] [Eq : LEq P T] (A : PAdd L N Eq)
  := A.toAddNatSuccEqSucc.addNatSuccEqSucc
def AmSn_eq_SAmn {P : Sort u} {T : Type v} 
  {L : Logic P} [N : Nat P T] [Eq : LEq P T] (A : PAdd L N Eq)
  {a b : T} := A.toAddNatSuccEqSucc.addNatSuccEqSucc a b
end PAdd

end Gaea.Peano
