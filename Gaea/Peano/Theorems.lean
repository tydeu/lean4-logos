import Gaea.Logic
import Gaea.Syntax
import Gaea.Syntax.Notation
import Gaea.Logic.Rules
import Gaea.Peano.Rules

universes u v w

open Gaea.Syntax
open Gaea.Logic.Rules
open Gaea.Peano.Rules

namespace Gaea.Peano

--------------------------------------------------------------------------------
-- General Theorems
--------------------------------------------------------------------------------

def natCases 
{P : Sort u} {L : Logic P} {T : Type v} 
[Nat P T] [Zero T] [Succ T]
(natInduction : NatInduction L T)
: (f : T -> P) -> 
  (L |- f 0) -> ((n : T) -> (L |- nat n) -> (L |- f (S n))) -> 
    ((n : T) -> (L |- nat n) -> (L |- f n))
:= by
  intro f f0 fS n nat_n
  have ih : (n : T) -> (L |- nat n) -> (L |- f n) -> (L |- f (S n)) := 
    fun n nat_n fn => fS n nat_n
  exact natInduction f f0 ih n nat_n

--------------------------------------------------------------------------------
-- Addition Theorems
--------------------------------------------------------------------------------

theorem addZeroEqZero 
{P : Sort u} {L : Logic P} {T : Type v} 
[LEq P T] [Nat P T] [Zero T] [Add T] 
(nat_0 : NatZero L T) 
(An0_eq_n : AddNatZeroEqNat L T)
: L |- 0 + 0 = (0 : T) 
:= An0_eq_n 0 nat_0

theorem natAddNatZero
{P : Sort u} {L : Logic P} {T : Type v} 
[LEq P T] [Nat P T] [Zero T] [Add T] 
(natEq : NatEq L T) 
(An0_eq_n : AddNatZeroEqNat L T)
: (a : T) -> (L |- nat a) -> (L |- nat (a + 0))
:= by
  intro a nat_a
  apply natEq _ a nat_a
  exact An0_eq_n a nat_a

-- Uses standard (predicate) induction
theorem NatAddNat_induct
{P : Sort u} {L : Logic P} {T : Type v} 
[LForall P T] [LIf P] [LEq P T] [Nat P T] [Zero T] [Succ T] [Add T]
(ifIntro : IfIntro L)
(ifElim : IfElim L)
(forallIntro : ForallIntro L T)
(forallElim : ForallElim L T)
(nat_S : NatSuccNat L T) 
(natEq : NatEq L T) 
(natInduction : NatInduction L T)
(An0_eq_n : AddNatZeroEqNat L T)
(AnS_eq_S : AddNatSuccEqSucc L T)
: (b : T) -> (L |- nat b) -> (L |- forall (a : T) => nat a -> nat (a + b))
:= by
  intro b nat_b
  apply natInduction 
    (fun b => forall (a : T) => nat a -> nat (a + b))
  -- Base
  apply forallIntro; intro a
  apply ifIntro; intro nat_a
  exact natAddNatZero natEq An0_eq_n a nat_a
  -- Induction
  intro a nat_a p_ih
  apply forallIntro; intro b
  apply ifIntro; intro nat_b
  have nat_Aba := ifElim _ _ (forallElim _ p_ih b) nat_b 
  have abSa_eq_Saba := AnS_eq_S _ _ nat_b nat_a
  have nat_SAba := nat_S _ nat_Aba
  exact natEq _ _ nat_SAba abSa_eq_Saba
  exact nat_b

theorem NatAddNat
{P : Sort u} {L : Logic P} {T : Type v} 
[LForall P T] [LIf P] [LEq P T] [Nat P T] [Zero T] [Succ T] [Add T]
(ifIntro : IfIntro L)
(ifElim : IfElim L)
(forallIntro : ForallIntro L T)
(forallElim : ForallElim L T)
(nat_S : NatSuccNat L T) 
(natEq : NatEq L T) 
(natInduction : NatInduction L T)
(An0_eq_n : AddNatZeroEqNat L T)
(AnS_eq_S : AddNatSuccEqSucc L T)
: (a b : T) -> (L |- nat a) -> (L |- nat b) -> (L |- nat (a + b))
:= by
  intro a b nat_a nat_b
  have h :=  NatAddNat_induct ifIntro ifElim forallIntro forallElim  
    nat_S natEq natInduction An0_eq_n AnS_eq_S b nat_b
  exact ifElim _ _ (forallElim _ h a) nat_a

-- Uses schema induction
theorem NatAddNat'
{P : Sort u} {L : Logic.{u,w} P} {T : Type v} 
[LEq P T] [Nat P T] [Zero T] [Succ T] [Add T]
(nat_S : NatSuccNat L T) 
(natEq : NatEq L T) 
(natInduction : NatInduction'.{u,v,(imax (v+1) w)} L T)
(An0_eq_n : AddNatZeroEqNat L T)
(AnS_eq_S : AddNatSuccEqSucc L T)
: (a b : T) -> (L |- nat a) -> (L |- nat b) -> (L |- nat (a + b))
:= by
  intro m n nat_m nat_n
  apply natInduction
    (fun b => (a : T) -> (L |- nat a) -> (L |- nat (a + b)))
  -- Base
  intro a nat_a
  exact natAddNatZero natEq An0_eq_n a nat_a
  -- Induction
  intro a nat_a ih b nat_b
  have nat_Aba := ih b nat_b 
  have abSa_eq_Saba := AnS_eq_S _ _ nat_b nat_a
  have nat_SAba := nat_S _ nat_Aba
  exact natEq _ _ nat_SAba abSa_eq_Saba
  exact nat_n; exact nat_m

end Gaea.Peano