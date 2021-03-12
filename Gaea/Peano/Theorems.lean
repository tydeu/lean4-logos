import Gaea.Logic
import Gaea.Syntax
import Gaea.Syntax.Notation
import Gaea.Logic.Rules
import Gaea.Peano.Rules

universes u v w

namespace Gaea.Peano

open Gaea.Syntax
open Gaea.Logic.Rules
open Gaea.Peano.Rules

-- General Theorems

def natCases 
{P : Sort u} {L : Logic P} {N : Type v} 
[Nat P N] [Zero N] [Succ N]
(natInduction : NatInduction L N)
: (f : N -> P) -> 
  (L |- f 0) -> ((n : N) -> (L |- nat n) -> (L |- f (S n))) -> 
    ((n : N) -> (L |- nat n) -> (L |- f n))
:= by
  intro f f0 fS n nat_n
  have ih : (n : N) -> (L |- nat n) -> (L |- f n) -> (L |- f (S n)) := 
    fun n nat_n fn => fS n nat_n
  exact natInduction f f0 ih n nat_n

-- Addition Theorems

theorem addZeroEqZero 
{P : Sort u} {L : Logic P} {N : Type v} 
[LEq P N] [Nat P N] [Zero N] [Add N] 
(nat_0 : NatZero L N) 
(An0_eq_n : AddNatZeroEqNat L N)
: L |- 0 + 0 = (0 : N) 
:= An0_eq_n 0 nat_0

theorem natAddNatZero
{P : Sort u} {L : Logic P} {N : Type v} 
[LEq P N] [Nat P N] [Zero N] [Add N] 
(natEq : NatEq L N) 
(An0_eq_n : AddNatZeroEqNat L N)
: (a : N) -> (L |- nat a) -> (L |- nat (a + 0))
:= by
  intro a nat_a
  apply natEq _ a nat_a
  exact An0_eq_n a nat_a

theorem NatAddNat_induct
{P : Sort u} {L : Logic P} {N : Type v} 
[LForall P N] [LIf P] [LEq P N] [Nat P N] [Zero N] [Succ N] [Add N]
(ifIntro : IfIntro L)
(ifElim : IfElim L)
(forallIntro : ForallIntro L N)
(forallElim : ForallElim L N)
(nat_S : NatSuccNat L N) 
(natEq : NatEq L N) 
(natInduction : NatInduction L N)
(An0_eq_n : AddNatZeroEqNat L N)
(AnS_eq_S : AddNatSuccEqSucc L N)
: (b : N) -> (L |- nat b) -> (L |- forall (a : N) => nat a -> nat (a + b))
:= by
  intro b nat_b
  apply natInduction 
    (fun b => forall (a : N) => nat a -> nat (a + b))
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

theorem NatAddNat'
{P : Sort u} {L : Logic.{u,w} P} {N : Type v} 
[LEq P N] [Nat P N] [Zero N] [Succ N] [Add N]
(nat_S : NatSuccNat L N) 
(natEq : NatEq L N) 
(natInduction : NatInduction'.{u,v,(imax (v+1) w)} L N)
(An0_eq_n : AddNatZeroEqNat L N)
(AnS_eq_S : AddNatSuccEqSucc L N)
: (a b : N) -> (L |- nat a) -> (L |- nat b) -> (L |- nat (a + b))
:= by
  intro m n nat_m nat_n
  apply natInduction
    (fun b => (a : N) -> (L |- nat a) -> (L |- nat (a + b)))
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

theorem NatAddNat
{P : Sort u} {L : Logic P} {N : Type v} 
[LForall P N] [LIf P] [LEq P N] [Nat P N] [Zero N] [Succ N] [Add N]
(ifIntro : IfIntro L)
(ifElim : IfElim L)
(forallIntro : ForallIntro L N)
(forallElim : ForallElim L N)
(nat_S : NatSuccNat L N) 
(natEq : NatEq L N) 
(natInduction : NatInduction L N)
(An0_eq_n : AddNatZeroEqNat L N)
(AnS_eq_S : AddNatSuccEqSucc L N)
: (a b : N) -> (L |- nat a) -> (L |- nat b) -> (L |- nat (a + b))
:= by
  intro a b nat_a nat_b
  have h :=  NatAddNat_induct ifIntro ifElim forallIntro forallElim  
    nat_S natEq natInduction An0_eq_n AnS_eq_S b nat_b
  exact ifElim _ _ (forallElim _ h a) nat_a

end Gaea.Peano