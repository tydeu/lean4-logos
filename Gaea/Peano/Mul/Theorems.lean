import Gaea.Logic
import Gaea.Peano.Eq
import Gaea.Peano.Add
import Gaea.Peano.Rules
import Gaea.Peano.Forall
import Gaea.Peano.Induction
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
:= {natMulNatZero := fun a Na => K.natMulNat a 0 Na nat0}

-- nat (0 * a)

def natMulZeroNat_proof
{P : Sort u} {T : Type v} {L : Logic P}
[N : IsNat P T] [Q : LEq P T] [M : Mul T] [Z : Zero T]  
[NatZero L N Z] [NatEqNat L N Q] [MulZeroNatEqZero L N Q M Z]
: (a : T) -> (L |- nat a) -> (L |- nat (0 * a))
:= by intro a Na; apply natEq nat0; exact mulZeroNatEqZero Na

instance natMulZeroNat_inst 
{P : Sort u} {T : Type v} {L : Logic P}
[N : IsNat P T] [Q : LEq P T] [M : Mul T] [Z : Zero T]  
[NatZero L N Z] [NatEqNat L N Q] [MulZeroNatEqZero L N Q M Z]
: NatMulZeroNat L N M Z := {natMulZeroNat := natMulZeroNat_proof}

instance natMulZeroNat_spec 
{P : Sort u} {T : Type v} {L : Logic P} 
[N : IsNat P T] [M : Mul T] [Z : Zero T] 
[NatZero L N Z] [K : NatMulNat L N M] : NatMulZeroNat L N M Z 
:= {natMulZeroNat := fun a Na => K.natMulNat 0 a nat0 Na}

-- nat (a * b)

def natMulNat_proof
{P : Sort u} {T : Type v} {L : Logic P}
[N : PNat P T] [Q : LEq P T] [M : Mul T] [A : Add T]
[NatInductionRight L N] 
[NatEqNat L N.toIsNat Q]
[NatAddNat L N.toIsNat A]
[NatMulNatZero L N.toIsNat M N.toZero]
[MulNatZeroEqZero L N.toIsNat Q M N.toZero]
[MulNatSuccEqAddMul L N.toIsNat Q M A N.toSucc]
: (a b : T) -> (L |- nat a) -> (L |- nat b) -> (L |- nat (a * b))
:= by
  refine natInductionRight ?f0 ?fS
  case f0 =>
    intro a Na 
    exact natMulNatZero Na
  case fS =>
    intro a b Na Nb NMab
    have MaSb_eq_AaSMab := mulNatSuccEqAddMul Na Nb
    refine natEq ?_ MaSb_eq_AaSMab
    exact natAdd Na NMab

instance natMulNat_inst 
{P : Sort u} {T : Type v} {L : Logic P} 
[N : PNat P T] [Q : LEq P T] [M : Mul T] [A : Add T]
[NatInductionRight L N] 
[NatEqNat L N.toIsNat Q]
[NatZero L N.toIsNat N.toZero]
[NatAddNat L N.toIsNat A]
[MulNatZeroEqZero L N.toIsNat Q M N.toZero]
[MulNatSuccEqAddMul L N.toIsNat Q M A N.toSucc]
: NatMulNat L N.toIsNat M := {natMulNat := natMulNat_proof}

--------------------------------------------------------------------------------
-- Special Cases
--------------------------------------------------------------------------------

-- 0 * 0 = 0

instance mulZeroEqZero_spec_mulNatZero
{P : Sort u} {T : Type v} {L : Logic P}
[N : IsNat P T] [Q : LEq P T] [M : Mul T] [Z : Zero T] 
[NatZero L N Z] [MulNatZeroEqZero L N Q M Z]
: MulZeroEqZero L Q M Z
:= {mulZeroEqZero := mulNatZeroEqZero nat0}

instance mulZeroEqZero_spec_mulZeroNat
{P : Sort u} {T : Type v} {L : Logic P}
[N : IsNat P T] [Q : LEq P T] [M : Mul T] [Z : Zero T] 
[NatZero L N Z] [MulZeroNatEqZero L N Q M Z]
: MulZeroEqZero L Q M Z
:= {mulZeroEqZero := mulZeroNatEqZero nat0}

--------------------------------------------------------------------------------
-- Commuted Axioms
--------------------------------------------------------------------------------

-- 0 * a = 0

def mulZeroNatEqZero_proof {P : Sort u} {T : Type v} {L : Logic P} 
[N : PNat P T] [Q : LEq P T] [M : Mul T] [A : Add T]
[NatInduction L N]
[NatZero L N.toIsNat N.toZero]
[NatSuccNat L N.toIsNat N.toSucc]
[NatMulZeroNat L N.toIsNat M N.toZero]
[NatAddZeroNat L N.toIsNat A N.toZero]
[EqNatTrans L N.toIsNat Q]
[MulZeroEqZero L Q M N.toZero]
[AddZeroNatEqNat L N.toIsNat Q A N.toZero]
[MulNatSuccEqAddMul L N.toIsNat Q M A N.toSucc]
: (a : T) -> (L |- nat a) -> (L |- 0 * a = 0) 
:= by
  refine natInduction ?f0 ?fS
  case f0 => exact mulZeroEqZero
  case fS =>
    intro a Na M0a_eq_0
    have NSa := natS Na
    have NM0a := natMulZeroNat Na
    have NM0Sa := natMulZeroNat NSa
    have NA0M0a := natAddZeroNat NM0a
    apply eqNatTrans' NA0M0a NM0Sa nat0
    exact mulNatSuccEqAddMul nat0 Na
    apply eqNatTrans' NM0a NA0M0a nat0
    exact addZeroNatEqNat NM0a
    exact M0a_eq_0

instance mulZeroNatEqZero_inst {P : Sort u} {T : Type v} {L : Logic P} 
[N : PNat P T] [Q : LEq P T] [M : Mul T] [A : Add T]
[NatInduction L N]
[NatZero L N.toIsNat N.toZero]
[NatSuccNat L N.toIsNat N.toSucc]
[NatMulZeroNat L N.toIsNat M N.toZero]
[NatAddZeroNat L N.toIsNat A N.toZero]
[EqNatTrans L N.toIsNat Q]
[MulZeroEqZero L Q M N.toZero]
[AddZeroNatEqNat L N.toIsNat Q A N.toZero]
[MulNatSuccEqAddMul L N.toIsNat Q M A N.toSucc]
: MulZeroNatEqZero L N.toIsNat Q M N.toZero
:= {mulZeroNatEqZero := mulZeroNatEqZero_proof}

-- S a + b = b + (a * b)

def mulSuccNatEqAddMul_proof {P : Sort u} {T : Type v} {L : Logic P} 
[N : PNat P T] [Q : LEq P T] [M : Mul T] [A : Add T] [FaN : MForallNat L N.toIsNat]
[NatInduction L N]
[NatZero L N.toIsNat N.toZero]
[NatSuccNat L N.toIsNat N.toSucc]
[NatAddNat L N.toIsNat A]  
[NatMulNat L N.toIsNat M]
[EqNatTrans L N.toIsNat Q]
[EqNatLeftEuc L N.toIsNat Q]
[EqNatToEqSucc L N.toIsNat Q N.toSucc]
[EqNatAddNatLeft L N.toIsNat Q A]
[EqNatAddNatRight L N.toIsNat Q A]
[AddNatZeroEqNat L N.toIsNat Q A N.toZero]
[AddNatSuccEqSucc L N.toIsNat Q A N.toSucc]
[MulNatZeroEqZero L N.toIsNat Q M N.toZero]
[MulNatSuccEqAddMul L N.toIsNat Q M A N.toSucc]
: (a b : T) -> (L |- nat a) -> (L |- nat b) ->  (L |- S a * b = b + (a * b))
:= by
  refine natInductionRight ?f0 ?fS
  case f0 =>
    intro a Na
    have NSa := natS Na
    have NMa0 := natMulNatZero Na
    have NA0Ma0 := natAddZeroNat NMa0
    apply eqNatLeftEuc nat0 
      (natMulNatZero NSa) NA0Ma0
    exact mulNatZeroEqZero NSa
    apply eqNatTrans' NMa0 NA0Ma0 nat0
    exact addZeroNatEqNat NMa0
    exact mulNatZeroEqZero Na
  case fS =>
    intro a b Na Nb MSab_eq_AbMab
    have NSa := natS Na 
    have NSb := natS Nb
    have NMab := natMul Na Nb
    have NMSaSb := natMul NSa NSb
    have NASbMaSb := natAdd NSb (natMul Na NSb)
    have NSAab := natS (natAdd Na Nb)
    have NASAabMab := natAdd NSAab NMab 
    have NMSab := natMul NSa Nb
    have NAbMab := natAdd Nb NMab
    have NAaAbMab := natAdd Na NAbMab
    have NSAaAbMab := natS NAaAbMab
    have MSaSb_eq_ASaMSab := mulNatSuccEqAddMul NSa Nb
    refine eqNatLeftEuc NSAaAbMab NMSaSb NASbMaSb 
      ?MSaSb_eq_SAaAbMab ?ASbMaSb_eq_SAaAbMab
    case MSaSb_eq_SAaAbMab =>
      have NASaMSab := natAdd NSa NMSab
      have NASaAbMab := natAdd NSa NAbMab
      apply eqNatTrans' NASaMSab NMSaSb NSAaAbMab
      exact mulNatSuccEqAddMul NSa Nb
      apply eqNatTrans' NASaAbMab NASaMSab NSAaAbMab
      apply eqNatAddNatLeft' NSa NMSab NAbMab
      exact MSab_eq_AbMab
      exact addSuccNatEqSucc Na NAbMab
    case ASbMaSb_eq_SAaAbMab =>
      have NMaSb := natMul Na NSb
      have NAaMab := natAdd Na NMab
      have NAbAaMab := natAdd Nb NAaMab
      have NSAbAaMab := natS NAbAaMab
      have NASbAaMab := natAdd NSb NAaMab
      have NAba := natAdd Nb Na
      have NAAbaMab := natAdd NAba NMab
      have NAab := natAdd Na Nb
      have NAaSb := natAdd Na NSb
      have NASba := natAdd NSb Na
      have NAASbaMab := natAdd NASba NMab
      have NAAabMab := natAdd NAab NMab
      apply eqNatTrans' NASbAaMab NASbMaSb NSAaAbMab
      apply eqNatAddNatLeft' NSb NMaSb NAaMab
      exact mulNatSuccEqAddMul Na Nb
      apply eqNatTrans' NSAbAaMab NASbAaMab NSAaAbMab
      exact addSuccNatEqSucc Nb NAaMab
      apply eqNatToEqSucc NAbAaMab NAaAbMab
      apply eqNatTrans' NAAbaMab NAbAaMab NAaAbMab
      exact addNatAssocRev Nb Na NMab
      apply eqNatTrans' NAAabMab NAAbaMab NAaAbMab
      apply eqNatAddNatRight' NMab NAba NAab
      exact addNatComm Nb Na
      exact addNatAssoc Na Nb NMab

instance mulSuccNatEqAddMul_inst {P : Sort u} {T : Type v} {L : Logic P} 
[N : PNat P T] [Q : LEq P T] [M : Mul T] [A : Add T] [FaN : MForallNat L N.toIsNat]
[NatInduction L N]
[NatZero L N.toIsNat N.toZero]
[NatSuccNat L N.toIsNat N.toSucc]
[NatAddNat L N.toIsNat A]  
[NatMulNat L N.toIsNat M]
[EqNatSymm L N.toIsNat Q]
[EqNatTrans L N.toIsNat Q]
[EqNatToEqSucc L N.toIsNat Q N.toSucc]
[EqNatAddNatLeft L N.toIsNat Q A]
[EqNatAddNatRight L N.toIsNat Q A]
[AddNatZeroEqNat L N.toIsNat Q A N.toZero]
[AddNatSuccEqSucc L N.toIsNat Q A N.toSucc]
[MulNatZeroEqZero L N.toIsNat Q M N.toZero]
[MulNatSuccEqAddMul L N.toIsNat Q M A N.toSucc]
: MulSuccNatEqAddMul L N.toIsNat Q M A N.toSucc
:= {mulSuccNatEqAddMul := mulSuccNatEqAddMul_proof}

--------------------------------------------------------------------------------
-- Commutativity
--------------------------------------------------------------------------------

-- a * 0 = 0 * a

def mulNatZeroComm_proof {P : Sort u} {T : Type v} {L : Logic P} 
[N : IsNat P T] [Q : LEq P T] [M : Mul T] [A : Add T] [Z : Zero T]
[EqNatLeftEuc L N Q]
[NatZero L N Z]
[NatMulNatZero L N M Z]
[NatMulZeroNat L N M Z]
[MulZeroNatEqZero L N Q M Z]
[MulNatZeroEqZero L N Q M Z]
: (a : T) -> (L |- nat a) -> (L |- a * 0 = 0 * a) 
:= by
  intro a Na
  apply eqNatLeftEuc nat0 
  exact natMulNatZero Na; exact natMulZeroNat Na
  exact mulNatZeroEqZero Na; exact mulZeroNatEqZero Na

instance mulNatZeroComm_inst {P : Sort u} {T : Type v} {L : Logic P} 
[N : IsNat P T] [Q : LEq P T] [M : Mul T] [A : Add T] [Z : Zero T]
[EqNatLeftEuc L N Q]
[NatZero L N Z]
[NatMulNatZero L N M Z]
[NatMulZeroNat L N M Z]
[MulZeroNatEqZero L N Q M Z]
[MulNatZeroEqZero L N Q M Z]
: MulNatZeroComm L N Q M Z
:= {mulNatZeroComm := mulNatZeroComm_proof}

-- a * b = b * a

def mulNatComm_proof {P : Sort u} {T : Type v} {L : Logic P} 
[N : PNat P T] [Q : LEq P T] [M : Mul T] [A : Add T]
[NatInductionRight L N]
[NatAddNat L N.toIsNat A]  
[NatMulNat L N.toIsNat M]
[NatSuccNat L N.toIsNat N.toSucc]
[EqNatSymm L N.toIsNat Q]
[EqNatTrans L N.toIsNat Q]
[EqNatAddNatLeft L N.toIsNat Q A]
[MulNatZeroComm L N.toIsNat Q M N.toZero]
[MulSuccNatEqAddMul L N.toIsNat Q M A N.toSucc]
[MulNatSuccEqAddMul L N.toIsNat Q M A N.toSucc]
: (a b : T) -> (L |- nat a) -> (L |- nat b) -> (L |- a * b = b * a) 
:= by
  refine natInductionRight ?f0 ?fS
  case f0 =>
    intro a Na
    exact mulNatZeroComm Na
  case fS =>
    intro a b Na Nb Mab_eq_Mba
    have NSb := natS Nb
    have NMab := natMul Na Nb 
    have NAaMab := natAdd Na NMab
    have NMba := natMul Nb Na 
    have NAaMba := natAdd Na NMba
    have NSMba := natS NMba
    have NMSba := natMul NSb Na
    have NMSab := natMul Na NSb
    apply eqNatLeftEuc NAaMab NMSab NMSba
    exact mulNatSuccEqAddMul Na Nb
    apply eqNatTrans' NAaMba NMSba NAaMab
    exact mulSuccNatEqAddMul Nb Na
    apply eqNatAddNatLeft' Na NMba NMab
    apply eqNatSymm NMab NMba
    exact Mab_eq_Mba

instance mulNatComm_inst 
{P : Sort u} {T : Type v} {L : Logic P} 
[N : PNat P T] [Q : LEq P T] [M : Mul T] [A : Add T] 
[NatInductionRight L N]
[NatAddNat L N.toIsNat A]  
[NatMulNat L N.toIsNat M]
[NatSuccNat L N.toIsNat N.toSucc]
[EqNatSymm L N.toIsNat Q]
[EqNatTrans L N.toIsNat Q]
[EqNatAddNatLeft L N.toIsNat Q A]
[MulNatZeroComm L N.toIsNat Q M N.toZero]
[MulSuccNatEqAddMul L N.toIsNat Q M A N.toSucc]
[MulNatSuccEqAddMul L N.toIsNat Q M A N.toSucc]
: MulNatComm L N.toIsNat Q M 
:= {mulNatComm := mulNatComm_proof}

end Gaea.Peano