import Gaea.Logic
import Gaea.Peano.Eq
import Gaea.Peano.Add
import Gaea.Peano.Rules
import Gaea.Peano.Forall
import Gaea.Peano.Mul.Rules

universes u v w

open Gaea.Math
open Gaea.Logic

namespace Gaea.Peano

--------------------------------------------------------------------------------
-- Closure
--------------------------------------------------------------------------------

-- nat (a * 0)

def natMulNatZero_proof
{P : Sort u} {T : Type v} {L : Logic P}
[N : IsNat P T] [Q : LEq P T] [M : Mul T] [Z : Zero T]  
[NatZero L N Z] [NatEqNat L N Q] [MulNatZeroEqZero L N Q M Z]
: (a : T) -> (L |- nat a) -> (L |- nat (a * 0))
:= by intro a Na; apply natEq nat0; exact mulNatZeroEqZero Na

instance natMulNatZero_inst 
{P : Sort u} {T : Type v} {L : Logic P}
[N : IsNat P T] [Q : LEq P T] [M : Mul T] [Z : Zero T]  
[NatZero L N Z] [NatEqNat L N Q] [MulNatZeroEqZero L N Q M Z]
: NatMulNatZero L N M Z := {natMulNatZero := natMulNatZero_proof}

instance natMulNatZero_spec 
{P : Sort u} {T : Type v} {L : Logic P} 
[N : IsNat P T] [M : Mul T] [Z : Zero T] 
[NatZero L N Z] [K : NatMulNat L N M] : NatMulNatZero L N M Z 
:= {natMulNatZero := fun a Na => K.natMulNat a 0 Na nat0 }

-- nat (a * b)

def natMulNat_induct 
{P : Sort u} {T : Type v} {L : Logic P}
[N : PNat P T] [Q : LEq P T] [M : Mul T] [A : Add T] [FaN : MForallNat L N.toIsNat]
[NatInduction L N] 
[NatEqNat L N.toIsNat Q]
[NatAddNat L N.toIsNat A]
[NatSuccNat L N.toIsNat N.toSucc]
[NatMulNatZero L N.toIsNat M N.toZero]
[MulNatZeroEqZero L N.toIsNat Q M N.toZero]
[MulNatSuccEqAddMul L N.toIsNat Q M A N.toSucc]
: (b : T) -> (L |- nat b) -> (L |- forallNat (a : T) => nat (a * b))
:= by
  refine natInduction ?f0 ?fS
  case f0 =>
    apply forallNatIntro; intro a Na 
    exact natMulNatZero Na
  case fS =>
    intro b Nb p_Nn_to_NMnb
    apply forallNatIntro; intro a Na
    have MaSb_eq_AaSMab := mulNatSuccEqAddMul Na Nb
    refine natEq ?_ MaSb_eq_AaSMab
    have NMab := forallNatElim p_Nn_to_NMnb Na
    exact natAdd Na (natS NMab) 

def natMulNat_proof {P : Sort u} {T : Type v} {L : Logic P} 
[N : PNat P T] [Q : LEq P T] [M : Mul T] [A : Add T] [Fa : MForall L T] [If : MIf L]
[NatInduction L N] 
[NatEqNat L N.toIsNat Q]
[NatZero L N.toIsNat N.toZero]
[NatSuccNat L N.toIsNat N.toSucc]
[NatAddNat L N.toIsNat A]
[MulNatZeroEqZero L N.toIsNat Q M N.toZero]
[MulNatSuccEqAddMul L N.toIsNat Q M A N.toSucc]
: (a b : T) -> (L |- nat a) -> (L |- nat b) -> (L |- nat (a * b))
:= fun a b Na Nb => forallNatElim (natMulNat_induct b Nb) Na

instance natMulNat_inst {P : Sort u} {T : Type v} {L : Logic P} 
[N : PNat P T] [Q : LEq P T] [M : Mul T] [A : Add T] [Fa : MForall L T] [If : MIf L]
[NatInduction L N] 
[NatEqNat L N.toIsNat Q]
[NatZero L N.toIsNat N.toZero]
[NatSuccNat L N.toIsNat N.toSucc]
[NatAddNat L N.toIsNat A]
[MulNatZeroEqZero L N.toIsNat Q M N.toZero]
[MulNatSuccEqAddMul L N.toIsNat Q M A N.toSucc]
: NatMulNat L N.toIsNat M := {natMulNat := natMulNat_proof}


end Gaea.Peano