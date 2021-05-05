import Gaea.Peano.Nat
import Gaea.Peano.Forall
import Gaea.Peano.Induction.Rules

universes u v

open Gaea.Notation
open Gaea.Peano.Notation

namespace Gaea.Peano

--------------------------------------------------------------------------------
-- Predicate Induction
--------------------------------------------------------------------------------

-- By Meta

def natInductionByMeta {P : Sort u} {T : Sort v} 
{L : Logic P} {N : PNat P T} (I : MetaNatInduction L N)
: (f : T -> P) -> (L |- f 0) -> 
  ((a : T) -> (L |- nat a) -> (L |- f a) -> (L |- f (S a))) ->
  ((a : T) -> (L |- nat a) -> (L |- f a))
:= by
  intro f f0 fS
  exact metaNatInduction L f0 fS 
    (f := fun a => L |- f a)

instance iNatInductionByMeta 
{P : Sort u} {T : Sort v} {L : Logic P} 
[N : PNat P T] [I : MetaNatInduction L N]
: NatInduction L N
:= {toFun := natInductionByMeta I}

-- By Right Binary Induction

def natInductionByRight {P : Sort u} {T : Sort v} 
{L : Logic P} {N : PNat P T} (I : NatInductionRight L N)
: (f : T -> P) -> (L |- f 0) -> 
  ((a : T) -> (L |- nat a) -> (L |- f a) -> (L |- f (S a))) ->
  ((a : T) -> (L |- nat a) -> (L |- f a))
:= by
  intro f f0 fS a Na
  refine natInductionRight (R := fun a b => f b) 
    ?f0' ?fS' a a Na Na
  case f0' => intro a Na; exact f0 
  case fS' => intro b Nb ih a Na; exact fS b Nb (ih a Na) 

instance iNatInductionByRight
{P : Sort u} {T : Sort v} {L : Logic P}
[N : PNat P T] [I : NatInductionRight L N]
: NatInduction L N
:= {toFun := natInductionByRight I}

--------------------------------------------------------------------------------
-- Left Binary Induction
--------------------------------------------------------------------------------

-- By Predicate Induction & SForallNat

def natInductionLeftByForallNat_induct
{P : Sort u} {T : Sort v} {L : Logic P} 
{N : PNat P T} (I : NatInduction L N) (FaN : LForallNat L N.toIsNat)
: (R : T -> T -> P) -> 
  (L |- forallNat b => R 0 b) -> 
  ((a : T) -> (L |- nat a) -> 
    (L |- forallNat b => R a b) -> 
    (L |- forallNat b => R (S a) b)) ->
  ((a : T) -> (L |- nat a) -> (L |- forallNat b => R a b))
:= by
  intro R p_f0 p_fS
  exact natInduction p_f0 p_fS

def natInductionLeftByForallNat 
{P : Sort u} {T : Sort v} {L : Logic P} 
{N : PNat P T} (I : NatInduction L N) (FaN : LForallNat L N.toIsNat)
: (R : Rel P T) -> 
  ((b : T) -> (L |- nat b) -> (L |- R 0 b)) -> 
  ((a : T) -> (L |- nat a) ->
    ((b : T) -> (L |- nat b) -> (L |- R a b)) -> 
    ((b : T) -> (L |- nat b) -> (L |- R (S a) b))) ->
  ((a b : T) -> (L |- nat a) -> (L |- nat b) -> (L |- R a b))
:= by
  intro R f0 fS a b Na Nb
  have h := natInductionLeftByForallNat_induct I FaN
    R ?p_f0 ?p_fS a Na
  case p_f0 =>
    apply FaN.intro; intro b Nb
    exact f0 b Nb
  case p_fS =>
    intro a Na p_ih
    apply FaN.intro; intro b Nb
    have ih := fun b (Nb : L |- nat b) => FaN.elim p_ih Nb
    exact fS a Na ih b Nb
  exact FaN.elim h Nb

instance iNatInductionLeftByForallNat
{P : Sort u} {T : Sort v} {L : Logic P}
[N : PNat P T] [I : NatInduction L N] [FaN : LForallNat L N.toIsNat]
: NatInductionLeft L N
:= {toFun := natInductionLeftByForallNat I FaN}

-- By Meta Induction

def natInductionLeftByMeta 
{P : Sort u} {T : Sort v} {L : Logic P} 
{N : PNat P T} (I : MetaNatInduction L N)
: (R : T -> T -> P) -> 
  ((b : T) -> (L |- nat b) -> (L |- R 0 b)) -> 
  ((a : T) -> (L |- nat a) ->
    ((b : T) -> (L |- nat b) -> (L |- R a b)) -> 
    ((b : T) -> (L |- nat b) -> (L |- R (S a) b))) ->
  ((a b : T) -> (L |- nat a) -> (L |- nat b) -> (L |- R a b))
:= by
  intro R f0 fS
  have h := metaNatInduction L f0 fS
    (f := fun (a : T) => (b : T) -> (L |- nat b) -> (L |- R a b)) 
  intro a b Na Nb
  exact h a Na b Nb

instance iNatInductionLeftByMeta
{P : Sort u} {T : Sort v} {L : Logic P}
[N : PNat P T] [I : MetaNatInduction L N]
: NatInductionLeft L N
:= {toFun := natInductionLeftByMeta I}

--------------------------------------------------------------------------------
-- Right Binary Induction
--------------------------------------------------------------------------------

-- By Predicate Induction & SForallNat

def natInductionRightByForallNat_induct
{P : Sort u} {T : Sort v} {L : Logic P} 
{N : PNat P T} (I : NatInduction L N) (FaN : LForallNat L N.toIsNat)
: (R : T -> T -> P) -> 
  (L |- forallNat a => R a 0) -> 
  ((b : T) -> (L |- nat b) -> 
    (L |- forallNat a => R a b) -> 
    (L |- forallNat a => R a (S b))) ->
  ((b : T) -> (L |- nat b) -> (L |- forallNat a => R a b))
:= by
  intro R p_f0 p_fS
  exact natInduction p_f0 p_fS

def natInductionRightByForallNat
{P : Sort u} {T : Sort v} {L : Logic P} 
{N : PNat P T} (I : NatInduction L N) (FaN : LForallNat L N.toIsNat)
: (R : T -> T -> P) -> 
  ((a : T) -> (L |- nat a) -> (L |- R a 0)) -> 
  ((b : T) -> (L |- nat b) -> 
    ((a : T) -> (L |- nat a) -> (L |- R a b)) -> 
    ((a : T) -> (L |- nat a) -> (L |- R a (S b)))) ->
  ((a b : T) -> (L |- nat a) -> (L |- nat b) -> (L |- R a b))
:= by
  intro R f0 fS a b Na Nb
  have h := natInductionRightByForallNat_induct I FaN
    R ?p_f0 ?p_fS b Nb
  case p_f0 =>
    apply FaN.intro; intro a Na
    exact f0 a Na
  case p_fS =>
    intro b Nb p_ih
    apply FaN.intro; intro a Na
    have ih := fun a (Na : L |- nat a) => FaN.elim p_ih Na
    exact fS b Nb ih a Na
  exact FaN.elim h Na

instance iNatInductionRightByForallNat
{P : Sort u} {T : Sort v} {L : Logic P}
[N : PNat P T] [I : NatInduction L N] [FaN : LForallNat L N.toIsNat]
: NatInductionRight L N
:= {toFun := natInductionRightByForallNat I FaN}

-- By Meta Induction

def natInductionRightByMeta 
{P : Sort u} {T : Sort v} {L : Logic P} 
{N : PNat P T} (I : MetaNatInduction L N)
: (R : T -> T -> P) -> 
  ((a : T) -> (L |- nat a) -> (L |- R a 0)) -> 
  ((b : T) -> (L |- nat b) -> 
    ((a : T) -> (L |- nat a) -> (L |- R a b)) -> 
    ((a : T) -> (L |- nat a) -> (L |- R a (S b)))) ->
  ((a b : T) -> (L |- nat a) -> (L |- nat b) -> (L |- R a b))
:= by
  intro R f0 fS
  have h := metaNatInduction L f0 fS
    (f := fun (b : T) => (a : T) -> (L |- nat a) -> (L |- R a b))
  intro a b Na Nb
  exact h b Nb a Na

instance iNatInductionRightByMeta
{P : Sort u} {T : Sort v} {L : Logic P}
[N : PNat P T] [I : MetaNatInduction L N]
: NatInductionRight L N
:= {toFun := natInductionRightByMeta I}

-- By Right Ternary Induction

def natInductionRightByRight3
{P : Sort u} {T : Sort v} {L : Logic P}
{N : PNat P T} (I : NatInductionRight3 L N)
: (R : T -> T -> P) -> 
  ((a : T) -> (L |- nat a) -> (L |- R a 0)) -> 
  ((b : T) -> (L |- nat b) -> 
    ((a : T) -> (L |- nat a) -> (L |- R a b)) -> 
    ((a : T) -> (L |- nat a) -> (L |- R a (S b)))) ->
  ((a b : T) -> (L |- nat a) -> (L |- nat b) -> (L |- R a b))
:= by
  intro R f0 fS a b Na Nb
  refine natInductionRight3 ?f0' ?fS' a a b Na Na Nb
    (R := fun a b c => R b c)
  case f0' => 
    intro a b Na Nb
    exact f0 b Nb
  case fS' => 
    intro c Nc ih a b Na Nb 
    exact fS c Nc (fun b Nb => ih a b Na Nb) b Nb

instance iNatInductionRightByRight3
{P : Sort u} {T : Sort v} {L : Logic P}
[N : PNat P T] [I : NatInductionRight3 L N]
: NatInductionRight L N
:= {toFun := natInductionRightByRight3 I}

--------------------------------------------------------------------------------
-- Right Ternary Induction
--------------------------------------------------------------------------------

-- By Predicate Induction & SForallNat

def natInductionRight3ByForallNat_induct
{P : Sort u} {T : Sort v} {L : Logic P} 
{N : PNat P T} (I : NatInduction L N) (FaN : LForallNat L N.toIsNat)
: (R : T -> T -> T -> P) -> 
  (L |- forallNat a b => R a b 0) -> 
  ((c : T) -> (L |- nat c) -> 
    (L |- forallNat a b => R a b c) -> 
    (L |- forallNat a b => R a b (S c))) ->
  ((c : T) -> (L |- nat c) -> (L |- forallNat a b => R a b c))
:= by
  intro R p_f0 p_fS
  exact natInduction p_f0 p_fS

def natInductionRight3ByForallNat
{P : Sort u} {T : Sort v} {L : Logic P} 
{N : PNat P T} (I : NatInduction L N) (FaN : LForallNat L N.toIsNat)
: (R : T -> T -> T -> P) -> 
  ((a b : T) -> (L |- nat a) -> (L |- nat b) -> 
    (L |- R a b 0)) -> 
  ((c : T) -> (L |- nat c) ->
    ((a b : T) -> (L |- nat a) -> (L |- nat b) -> (L |- R a b c)) -> 
    ((a b : T) -> (L |- nat a) -> (L |- nat b) -> (L |- R a b (S c)))) ->
  ((a b c : T) -> (L |- nat a) -> (L |- nat b) -> (L |- nat c) -> 
    (L |- R a b c))
:= by
  intro R f0 fS a b c Na Nb Nc
  have h := natInductionRight3ByForallNat_induct I FaN 
    R ?p_f0 ?p_fS c Nc
  case p_f0 =>
    apply FaN.intro; intro a Na
    apply FaN.intro; intro b Nb
    exact f0 a b Na Nb
  case p_fS =>
    intro c Nc p_ih
    apply FaN.intro; intro a Na
    apply FaN.intro; intro b Nb
    have ih := fun a b (Na : L |- nat a) (Nb : L |- nat b) => 
      FaN.elim (FaN.elim p_ih Na) Nb
    exact fS c Nc ih a b Na Nb
  exact FaN.elim (FaN.elim h Na) Nb

instance iNatInductionRight3ByForallNat
{P : Sort u} {T : Sort v} {L : Logic P}
[N : PNat P T] [I : NatInduction L N] [FaN : LForallNat L N.toIsNat]
: NatInductionRight3 L N
:= {toFun := natInductionRight3ByForallNat I FaN}

-- By Meta Induction

def natInductionRight3ByMeta
{P : Sort u} {T : Sort v} {L : Logic P} 
{N : PNat P T} (I : MetaNatInduction L N)
: (R : T -> T -> T -> P) -> 
  ((a b : T) -> (L |- nat a) -> (L |- nat b) ->  
    (L |- R a b 0)) -> 
  ((c : T) -> (L |- nat c) ->
    ((a b : T) -> (L |- nat a) -> (L |- nat b) -> (L |- R a b c)) -> 
    ((a b : T) -> (L |- nat a) -> (L |- nat b) -> (L |- R a b (S c)))) ->
  ((a b c : T) -> (L |- nat a) -> (L |- nat b) -> (L |- nat c) -> 
    (L |- R a b c))
:= by
  intro R f0 fS
  have h := metaNatInduction L f0 fS
    (f := fun (c : T) => 
      (a b : T) -> (L |- nat a) -> (L |- nat b) -> (L |- R a b c))
  intro a b c Na Nb Nc
  exact h c Nc a b Na Nb

instance iNatInductionRight3ByMeta
{P : Sort u} {T : Sort v} {L : Logic P}
[N : PNat P T] [I : MetaNatInduction L N]
: NatInductionRight3 L N
:= {toFun := natInductionRight3ByMeta I}

--------------------------------------------------------------------------------
-- Right Ternary Induction (Conditioned)
--------------------------------------------------------------------------------

-- By Predicate Induction & SForallNat & Ent

def natInductionRight3IfByForallNatIf_induct
{P : Sort u} {T : Sort v} {L : Logic P} {N : PNat P T} 
(I : NatInduction L N) (FaN : LForallNat L N.toIsNat) (ent : LEnt L)
: (C : T -> T -> P) -> (R : T -> T -> T -> P) ->
  (L |- forallNat a b => C a b -> R a b 0) -> 
  ((c : T) -> (L |- nat c) -> 
    (L |- forallNat a b => C a b -> R a b c) -> 
    (L |- forallNat a b => C a b -> R a b (S c))) ->
  ((c : T) -> (L |- nat c) -> (L |- forallNat a b => C a b -> R a b c))
:= by
  intro C R p_f0 p_fS
  exact natInduction p_f0 p_fS

def natInductionRight3IfByForallNatIf
{P : Sort u} {T : Sort v} {L : Logic P} {N : PNat P T} 
(I : NatInduction L N) (FaN : LForallNat L N.toIsNat) (ent : LEnt L)
: (C : T -> T -> P) -> (R : T -> T -> T -> P) ->
  ((a b : T) -> (L |- nat a) -> (L |- nat b) ->  
    (L |- C a b) -> (L |- R a b 0)) -> 
  ((c : T) -> (L |- nat c) -> 
    ((a b : T) -> (L |- nat a) -> (L |- nat b) -> 
      (L |- C a b) -> (L |- R a b c)) ->
    ((a b : T) -> (L |- nat a) -> (L |- nat b) -> 
      (L |- C a b) -> (L |- R a b (S c)))) ->
  ((a b c : T) -> (L |- nat a) -> (L |- nat b) -> (L |- nat c) -> 
    (L |- C a b) -> (L |- R a b c))
:= by
  intro C R f0 fS a b c Na Nb Nc
  have h := natInductionRight3IfByForallNatIf_induct I FaN ent
    C R ?p_f0 ?p_fS c Nc
  case p_f0 =>
    apply FaN.intro; intro a Na
    apply FaN.intro; intro b Nb
    apply ent.intro; intro Cab
    exact f0 a b Na Nb Cab
  case p_fS =>
    intro c Nc p_ih
    apply FaN.intro; intro a Na
    apply FaN.intro; intro b Nb
    apply ent.intro; intro Cab
    have ih := fun a b (Na : L |- nat a) (Nb : L |- nat b) Cab => 
      ent.elim (FaN.elim (FaN.elim p_ih Na) Nb) Cab
    exact fS c Nc ih a b Na Nb Cab
  exact ent.elim (FaN.elim (FaN.elim h Na) Nb)

instance iNatInductionRight3IfByForallNatIf
{P : Sort u} {T : Sort v} {L : Logic P} [N : PNat P T] 
[I : NatInduction L N] [FaN : LForallNat L N.toIsNat] [ent : LEnt L]
: NatInductionRight3If L N
:= {toFun := natInductionRight3IfByForallNatIf I FaN ent}

-- By Meta Induction

def natInductionRight3IfByMeta
{P : Sort u} {T : Sort v} {L : Logic P} 
{N : PNat P T} (I : MetaNatInduction L N)
: (C : T -> T -> P) -> (R : T -> T -> T -> P) ->
  ((a b : T) -> (L |- nat a) -> (L |- nat b) ->  
    (L |- C a b) -> (L |- R a b 0)) -> 
  ((c : T) -> (L |- nat c) -> 
    ((a b : T) -> (L |- nat a) -> (L |- nat b) -> 
      (L |- C a b) -> (L |- R a b c)) ->
    ((a b : T) -> (L |- nat a) -> (L |- nat b) -> 
      (L |- C a b) -> (L |- R a b (S c)))) ->
  ((a b c : T) -> (L |- nat a) -> (L |- nat b) -> (L |- nat c) -> 
    (L |- C a b) -> (L |- R a b c))
:= by
  intro C R f0 fS
  have h := metaNatInduction L f0 fS
    (f := fun (c : T) => (a b : T) -> (L |- nat a) -> (L |- nat b) -> 
      (L |- C a b) -> (L |- R a b c))
  intro a b c Na Nb Nc
  exact h c Nc a b Na Nb

instance iNatInductionRight3IfByMeta
{P : Sort u} {T : Sort v} {L : Logic P}
[N : PNat P T] [I : MetaNatInduction L N]
: NatInductionRight3If L N
:= {toFun := natInductionRight3IfByMeta I}
