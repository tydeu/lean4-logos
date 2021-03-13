import Gaea.Logic
import Gaea.Syntax
import Gaea.Syntax.Notation
import Gaea.Logic.Rules
import Gaea.Peano.Rules

universes u v w

open Gaea.Logic
open Gaea.Syntax
open Gaea.Logic.Rules
open Gaea.Peano.Rules

namespace Gaea.Peano

--------------------------------------------------------------------------------
-- General Theorems
--------------------------------------------------------------------------------

def natCases 
{P : Sort u} {T : Type v} {L : Logic P} 
[Z : Zero T] [Su : Succ T] [N : Nat P T] 
(natInduction : NatInduction L N Z Su)
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
{P : Sort u} {T : Type v} {L : Logic P}
[Eq : LEq P T] [A : Add T] [Z : Zero T] [N : Nat P T]
(nat_0 : NatZero L N Z) 
(An0_eq_n : AddNatZeroEqNat L N Eq A Z)
: L |- 0 + 0 = (0 : T) 
:= An0_eq_n 0 nat_0

theorem natAddNatZero
{P : Sort u} {T : Type v} {L : Logic P}
[Eq : LEq P T] [A : Add T] [Z : Zero T] [N : Nat P T] 
(natEq : NatEqNat L N Eq) 
(An0_eq_n : AddNatZeroEqNat L N Eq A Z)
: (a : T) -> (L |- nat a) -> (L |- nat (a + 0))
:= by
  intro a nat_a
  apply natEq _ a nat_a
  exact An0_eq_n a nat_a

-- Uses standard (predicate) induction
theorem natAddNat_induct
{P : Sort u} {T : Type v} {L : Logic P}
[N : Nat P T] [Eq : LEq P T] [A : Add T] [Z : Zero T] [Su : Succ T] 
[Fa : LForall P T] [If : LIf P] 
(ifIntro : IfIntro L If)
(ifElim : IfElim L If)
(forallIntro : ForallIntro L Fa)
(forallElim : ForallElim L Fa)
(natEq : NatEqNat L N Eq) 
(nat_S : NatSuccNat L N Su) 
(natInduction : NatInduction L N Z Su)
(An0_eq_n : AddNatZeroEqNat L N Eq A Z)
(AnS_eq_S : AddNatSuccEqSucc L N Eq A Su)
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
  intro a nat_a p_Nn_to_NAna
  apply forallIntro; intro b
  apply ifIntro; intro nat_b
  have nat_Aba := ifElim _ _ (forallElim _ p_Nn_to_NAna b) nat_b 
  have AbSa_eq_SAba := AnS_eq_S _ _ nat_b nat_a
  have nat_SAba := nat_S _ nat_Aba
  exact natEq _ _ nat_SAba AbSa_eq_SAba
  exact nat_b

theorem natAddNat
{P : Sort u} {T : Type v} {L : Logic P} 
[N : Nat P T] [Eq : LEq P T] [A : Add T] [Z : Zero T] [Su : Succ T]
[Fa : LForall P T] [If : LIf P] 
(ifIntro : IfIntro L If)
(ifElim : IfElim L If)
(forallIntro : ForallIntro L Fa)
(forallElim : ForallElim L Fa)
(natEq : NatEqNat L N Eq) 
(nat_S : NatSuccNat L N Su) 
(natInduction : NatInduction L N Z Su)
(An0_eq_n : AddNatZeroEqNat L N Eq A Z)
(AnS_eq_S : AddNatSuccEqSucc L N Eq A Su)
: (a b : T) -> (L |- nat a) -> (L |- nat b) -> (L |- nat (a + b))
:= by
  intro a b nat_a nat_b
  have h :=  natAddNat_induct ifIntro ifElim forallIntro forallElim  
    natEq nat_S natInduction An0_eq_n AnS_eq_S b nat_b
  exact ifElim _ _ (forallElim _ h a) nat_a

-- Uses schema induction
theorem natAddNat'
{P : Sort u} {T : Type v} {L : Logic.{u,w} P}
[N : Nat P T] [Eq : LEq P T]  [A : Add T] [Z : Zero T] [Su : Succ T] 
(natEq : NatEqNat L N Eq) 
(nat_S : NatSuccNat L N Su) 
(natInduction : NatInduction'.{u,v,(imax (v+1) w)} L N Z Su)
(An0_eq_n : AddNatZeroEqNat L N Eq A Z)
(AnS_eq_S : AddNatSuccEqSucc L N Eq A Su)
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