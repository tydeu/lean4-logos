import Gaea.Logic
import Gaea.Syntax
import Gaea.Peano.Rules
import Gaea.Peano.Modules

universes u v w

open Gaea.Logic
open Gaea.Syntax

namespace Gaea.Peano

--------------------------------------------------------------------------------
-- General Theorems
--------------------------------------------------------------------------------

theorem natCases 
{P : Sort u} {T : Type v} {L : Logic P} [N : Nat P T] [NatInduction L N]
: (f : T -> P) -> 
  (L |- f 0) -> ((n : T) -> (L |- nat n) -> (L |- f (S n))) -> 
    ((n : T) -> (L |- nat n) -> (L |- f n))
:= by
  intro f f0 fS n Nn
  have ih : (n : T) -> (L |- nat n) -> (L |- f n) -> (L |- f (S n)) := 
    fun n Nn fn => fS n Nn
  exact natInduction f f0 ih n Nn

--------------------------------------------------------------------------------
-- Addition Theorems
--------------------------------------------------------------------------------

theorem addZeroEqZero 
{P : Sort u} {T : Type v} {L : Logic P}
[Q : LEq P T] [A : Add T] [Z : Zero T] [N : IsNat P T]
[NatZero L N Z] [AddNatZeroEqNat L N Q A Z]
: L |- 0 + 0 = (0 : T) 
:= An0_eq_n nat0

theorem natAddNatZero
{P : Sort u} {T : Type v} {L : Logic P}
[Q : LEq P T] [A : Add T] [Z : Zero T] [N : IsNat P T] 
[NatEqNat L N Q] [AddNatZeroEqNat L N Q A Z]
: (a : T) -> (L |- nat a) -> (L |- nat (a + 0))
:= by intro a Na; apply natEq Na; exact An0_eq_n Na

-- Uses standard (predicate) induction
theorem natAddNat_induct {P : Sort u} {T : Type v} {L : Logic P}
[N : Nat P T] [Q : LEq P T] [A : PAdd L N Q] [Fa : MForall L T] [If : MIf L]
[NatEqNat L N.toIsNat Q] [NatSuccNat L N.toIsNat N.toSucc] [NatInduction L N]
: (b : T) -> (L |- nat b) -> (L |- forall (a : T) => nat a -> nat (a + b))
:= by
  intro n Nn
  apply natInduction 
    (fun b => forall (a : T) => nat a -> nat (a + b))
  exact forallNatIntro natAddNatZero
  -- Induction
  intro a Na p_Nn_to_NAna
  apply forallNatIntro; intro b Nb
  have AbSa_eq_SAba := AmSn_eq_SAmn Nb Na
  have NAba := forallNatElim p_Nn_to_NAna Nb 
  exact natEq (natS NAba) AbSa_eq_SAba
  exact Nn

theorem natAddNat {P : Sort u} {T : Type v} {L : Logic P} 
[N : Nat P T] [Q : LEq P T] [A : PAdd L N Q] [Fa : MForall L T] [If : MIf L]
[NatEqNat L N.toIsNat Q] [NatSuccNat L N.toIsNat N.toSucc] [NatInduction L N]
: (a b : T) -> (L |- nat a) -> (L |- nat b) -> (L |- nat (a + b))
:= fun a b Na Nb => forallNatElim (natAddNat_induct b Nb) Na

-- Uses schema induction
theorem natAddNat'
{P : Sort u} {T : Type v} {L : Logic.{u,w} P}
[N : Nat P T] [Q : LEq P T]  [A : PAdd L N Q]
[NatEqNat L N.toIsNat Q] [NatSuccNat L N.toIsNat N.toSucc] 
[NatInduction'.{u,v,(imax (v+1) w)} L N]
: (a b : T) -> (L |- nat a) -> (L |- nat b) -> (L |- nat (a + b))
:= by
  intro m n Nm Nn
  apply natInduction' L
    (fun (b : T) => (a : T) -> (L |- nat a) -> (L |- nat (a + b)))
  -- Base
  intro a Na
  exact natAddNatZero a Na
  -- Induction
  intro a Na ih b Nb
  have NAba := ih b Nb 
  have AbSa_eq_SAba := AmSn_eq_SAmn Nb Na
  have NSAba := natS NAba
  exact natEq NSAba AbSa_eq_SAba
  exact Nn; exact Nm

end Gaea.Peano