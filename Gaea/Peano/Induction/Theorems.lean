import Gaea.Peano.Nat
import Gaea.Math.Notation
import Gaea.Logic.Notation
import Gaea.Peano.Induction.Rules
import Gaea.Peano.Forall

universes u v

open Gaea.Math
open Gaea.Logic

namespace Gaea.Peano

--------------------------------------------------------------------------------
-- Predicate Induction
--------------------------------------------------------------------------------

-- By Schema

def natInduction_bySchema_proof
{P : Sort u} {T : Type v} {L : Logic P}
[N : PNat P T] [NatInduction' L N]
: (f : T -> P) -> (L |- f 0) -> 
  ((a : T) -> (L |- nat a) -> (L |- f a) -> (L |- f (S a))) ->
  ((a : T) -> (L |- nat a) -> (L |- f a))
:= by
  intro f f0 fS
  exact natInduction' L (fun a => L |- f a) f0 fS

instance natInduction_bySchema_inst
{P : Sort u} {T : Type v} {L : Logic P}
[N : PNat P T] [NatInduction' L N]
: NatInduction L N
:= {natInduction := natInduction_bySchema_proof}

-- By Right Binary Induction

def natInduction_byRightInduction_proof
{P : Sort u} {T : Type v} {L : Logic P}
[N : PNat P T] [NatInductionRight L N]
: (f : T -> P) -> (L |- f 0) -> 
  ((a : T) -> (L |- nat a) -> (L |- f a) -> (L |- f (S a))) ->
  ((a : T) -> (L |- nat a) -> (L |- f a))
:= by
  intro f f0 fS a Na
  refine natInductionRight (f := fun a b => f b) 
    ?f0' ?fS' a a Na Na
  case f0' => intro a Na; exact f0 
  case fS' => intro a b Na Nb; exact fS b Nb 

instance natInduction_byRightInduction_inst
{P : Sort u} {T : Type v} {L : Logic P}
[N : PNat P T] [NatInductionRight L N]
: NatInduction L N
:= {natInduction := natInduction_byRightInduction_proof}

--------------------------------------------------------------------------------
-- Left Binary Induction
--------------------------------------------------------------------------------

-- By Predicate Induction & ForallNat

def natInductionLeft_byForallNatPredicate_induct
{P : Sort u} {T : Type v} {L : Logic P}
[N : PNat P T] [NatInduction L N] [ForallNat P T]
: (f : T -> T -> P) -> 
  (L |- forallNat b => f 0 b) -> 
  ((a : T) -> (L |- nat a) -> 
    (L |- forallNat b => f a b) -> (L |- forallNat b => f (S a) b)) ->
  ((a : T) -> (L |- nat a) -> (L |- forallNat b => f a b))
:= by
  intro f p_f0 p_fS
  exact natInduction p_f0 p_fS

def natInductionLeft_byForallNatPredicate_proof
{P : Sort u} {T : Type v} {L : Logic P}
[N : PNat P T] [NatInduction L N] [MForallNat L N.toIsNat]
: (f : T -> T -> P) -> 
  ((b : T) -> (L |- nat b) -> (L |- f 0 b)) -> 
  ((a b : T) -> (L |- nat a) -> (L |- nat b) -> (L |- f a b) -> (L |- f (S a) b)) ->
  ((a b : T) -> (L |- nat a) -> (L |- nat b) -> (L |- f a b))
:= by
  intro f f0 fS a b Na Nb
  have h := natInductionLeft_byForallNatPredicate_induct 
    f ?p_f0 ?p_fS a Na
  case p_f0 =>
    apply forallNatIntro; intro b Nb
    exact f0 b Nb
  case p_fS =>
    intro a Na p_fab
    apply forallNatIntro; intro b Nb
    have fab := forallNatElim p_fab Nb
    exact fS a b Na Nb fab
  exact forallNatElim h Nb

instance natInductLeft_inst_forallNat
{P : Sort u} {T : Type v} {L : Logic P}
[N : PNat P T] [NatInduction L N] [MForallNat L N.toIsNat]
: NatInductionLeft L N
:= {natInductionLeft := natInductionLeft_byForallNatPredicate_proof}

-- By Schema Induction

def natInductionLeft_bySchema_proof
{P : Sort u} {T : Type v} {L : Logic P}
[N : PNat P T] [NatInduction' L N]
: (f : T -> T -> P) -> 
  ((b : T) -> (L |- nat b) -> (L |- f 0 b)) -> 
  ((a b : T) -> (L |- nat a) -> (L |- nat b) -> (L |- f a b) -> (L |- f (S a) b)) ->
  ((a b : T) -> (L |- nat a) -> (L |- nat b) -> (L |- f a b))
:= by
  intro f f0 fS
  have h := natInduction' L
    (fun (a : T) => (b : T) -> (L |- nat b) -> (L |- f a b)) f0 ?i_fS
  case i_fS =>
    intro a Na fan b Nb
    have fab := fan b Nb
    exact fS a b Na Nb fab
  intro a b Na Nb
  exact h a Na b Nb

instance natInductionLeft_bySchema_inst
{P : Sort u} {T : Type v} {L : Logic P}
[N : PNat P T] [NatInduction' L N]
: NatInductionLeft L N
:= {natInductionLeft := natInductionLeft_bySchema_proof}

--------------------------------------------------------------------------------
-- Right Binary Induction
--------------------------------------------------------------------------------

-- By Predicate Induction & ForallNat

def natInductionRight_byForallNatPredicate_induct
{P : Sort u} {T : Type v} {L : Logic P}
[N : PNat P T] [NatInduction L N] [ForallNat P T]
: (f : T -> T -> P) -> 
  (L |- forallNat a => f a 0) -> 
  ((b : T) -> (L |- nat b) -> 
    (L |- forallNat a => f a b) -> (L |- forallNat a => f a (S b))) ->
  ((b : T) -> (L |- nat b) -> (L |- forallNat a => f a b))
:= by
  intro f p_f0 p_fS
  exact natInduction p_f0 p_fS

def natInductionRight_byForallNatPredicate_proof
{P : Sort u} {T : Type v} {L : Logic P}
[N : PNat P T] [NatInduction L N] [MForallNat L N.toIsNat]
: (f : T -> T -> P) -> 
  ((a : T) -> (L |- nat a) -> (L |- f a 0)) -> 
  ((a b : T) -> (L |- nat a) -> (L |- nat b) -> (L |- f a b) -> (L |- f a (S b))) ->
  ((a b : T) -> (L |- nat a) -> (L |- nat b) -> (L |- f a b))
:= by
  intro f f0 fS a b Na Nb
  have h := natInductionRight_byForallNatPredicate_induct 
    f ?p_f0 ?p_fS b Nb
  case p_f0 =>
    apply forallNatIntro; intro a Na
    exact f0 a Na
  case p_fS =>
    intro b Nb p_fab
    apply forallNatIntro; intro a Na
    have fab := forallNatElim p_fab Na
    exact fS a b Na Nb fab
  exact forallNatElim h Na

instance natInductionRight_byForallNatPredicate_inst
{P : Sort u} {T : Type v} {L : Logic P}
[N : PNat P T] [NatInduction L N] [MForallNat L N.toIsNat]
: NatInductionRight L N
:= {natInductionRight := natInductionRight_byForallNatPredicate_proof}

-- By Schema Induction

def natInductionRight_bySchema_proof
{P : Sort u} {T : Type v} {L : Logic P}
[N : PNat P T] [NatInduction' L N]
: (f : T -> T -> P) -> 
  ((a : T) -> (L |- nat a) -> (L |- f a 0)) -> 
  ((a b : T) -> (L |- nat a) -> (L |- nat b) -> (L |- f a b) -> (L |- f a (S b))) ->
  ((a b : T) -> (L |- nat a) -> (L |- nat b) -> (L |- f a b))
:= by
  intro f f0 fS
  have h := natInduction' L
    (fun (b : T) => (a : T) -> (L |- nat a) -> (L |- f a b)) f0 ?i_fS
  case i_fS =>
    intro b Nb fnb a Na
    have fab := fnb a Na
    exact fS a b Na Nb fab
  intro a b Na Nb
  exact h b Nb a Na

instance natInductionRight_bySchema_inst
{P : Sort u} {T : Type v} {L : Logic P}
[N : PNat P T] [NatInduction' L N]
: NatInductionRight L N
:= {natInductionRight := natInductionRight_bySchema_proof}

-- By Right Ternery Induction

def natInductionRight_byRight3_proof
{P : Sort u} {T : Type v} {L : Logic P}
[N : PNat P T] [NatInductionRight3 L N]
: (f : T -> T -> P) -> 
  ((a : T) -> (L |- nat a) -> (L |- f a 0)) -> 
  ((a b : T) -> (L |- nat a) -> (L |- nat b) -> (L |- f a b) -> (L |- f a (S b))) ->
  ((a b : T) -> (L |- nat a) -> (L |- nat b) -> (L |- f a b))
:= by
  intro f f0 fS a b Na Nb
  refine natInductionRight3 (f := fun a b c => f b c) 
    ?f0' ?fS' a a b Na Na Nb
  case f0' => intro a b Na Nb; exact f0 b Nb
  case fS' => intro a b c Na Nb Nc; exact fS b c Nb Nc

instance natInductionRight_byRight3_inst
{P : Sort u} {T : Type v} {L : Logic P}
[N : PNat P T] [NatInductionRight3 L N]
: NatInductionRight L N
:= {natInductionRight := natInductionRight_byRight3_proof}

--------------------------------------------------------------------------------
-- Right Ternery Induction
--------------------------------------------------------------------------------

-- By Predicate Induction & ForallNat

def natInductionRight3_byForallNatPredicate_induct
{P : Sort u} {T : Type v} {L : Logic P}
[N : PNat P T] [NatInduction L N] [ForallNat P T]
: (f : T -> T -> T -> P) -> 
  (L |- forallNat a b => f a b 0) -> 
  ((c : T) -> (L |- nat c) -> 
    (L |- forallNat a b => f a b c) -> (L |- forallNat a b => f a b (S c))) ->
  ((c : T) -> (L |- nat c) -> (L |- forallNat a b => f a b c))
:= by
  intro f p_f0 p_fS
  exact natInduction p_f0 p_fS

def natInductionRight3_byForallNatPredicate_proof
{P : Sort u} {T : Type v} {L : Logic P}
[N : PNat P T] [NatInduction L N] [MForallNat L N.toIsNat]
: (f : T -> T -> T -> P) -> 
  ((a b : T) -> (L |- nat a) -> (L |- nat b) ->  
    (L |- f a b 0)) -> 
  ((a b c : T) -> (L |- nat a) -> (L |- nat b) -> (L |- nat c) ->
    (L |- f a b c) -> (L |- f a b (S c))) ->
  ((a b c : T) -> (L |- nat a) -> (L |- nat b) -> (L |- nat c) -> 
    (L |- f a b c))
:= by
  intro f f0 fS a b c Na Nb Nc
  have h := natInductionRight3_byForallNatPredicate_induct 
    f ?p_f0 ?p_fS c Nc
  case p_f0 =>
    apply forallNatIntro; intro a Na
    apply forallNatIntro; intro b Nb
    exact f0 a b Na Nb
  case p_fS =>
    intro c Nc p_fabc
    apply forallNatIntro; intro a Na
    apply forallNatIntro; intro b Nb
    have fabc := forallNatElim (forallNatElim p_fabc Na) Nb
    exact fS a b c Na Nb Nc fabc
  exact forallNatElim (forallNatElim h Na) Nb

instance natInductionRight3_byForallNatPredicate_inst
{P : Sort u} {T : Type v} {L : Logic P}
[N : PNat P T] [NatInduction L N] [MForallNat L N.toIsNat]
: NatInductionRight3 L N
:= {natInductionRight3 := natInductionRight3_byForallNatPredicate_proof}

-- By Schema Induction

def natInductionRight3_bySchema_proof
{P : Sort u} {T : Type v} {L : Logic P}
[N : PNat P T] [NatInduction' L N]
: (f : T -> T -> T -> P) -> 
  ((a b : T) -> (L |- nat a) -> (L |- nat b) ->  
    (L |- f a b 0)) -> 
  ((a b c : T) -> (L |- nat a) -> (L |- nat b) -> (L |- nat c) ->
    (L |- f a b c) -> (L |- f a b (S c))) ->
  ((a b c : T) -> (L |- nat a) -> (L |- nat b) -> (L |- nat c) -> 
    (L |- f a b c))
:= by
  intro f f0 fS
  have h := natInduction' L
    (fun (c : T) => (a b : T) -> (L |- nat a) -> (L |- nat b) -> (L |- f a b c)) 
    f0 ?i_fS
  case i_fS =>
    intro c Nc fmnc a b Na Nb
    have fabc := fmnc a b Na Nb
    exact fS a b c Na Nb Nc fabc
  intro a b c Na Nb Nc
  exact h c Nc a b Na Nb

instance natInductionRight3_bySchema_inst
{P : Sort u} {T : Type v} {L : Logic P}
[N : PNat P T] [NatInduction' L N]
: NatInductionRight3 L N
:= {natInductionRight3 := natInductionRight3_bySchema_proof}

end Gaea.Peano
