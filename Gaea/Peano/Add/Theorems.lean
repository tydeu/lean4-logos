import Gaea.Logic
import Gaea.Peano.Eq
import Gaea.Peano.One
import Gaea.Peano.Rules
import Gaea.Peano.Forall
import Gaea.Peano.Induction
import Gaea.Peano.Add.Rules

universes u v w

open Gaea.Math
open Gaea.Logic

namespace Gaea.Peano

--------------------------------------------------------------------------------
-- Closure
--------------------------------------------------------------------------------

-- nat (a + 0)

def natAddNatZero_proof
{P : Sort u} {T : Type v} {L : Logic P}
[N : IsNat P T] [Q : LEq P T] [A : Add T] [Z : Zero T]  
[NatEqNat L N Q] [AddNatZeroEqNat L N Q A Z]
: (a : T) -> (L |- nat a) -> (L |- nat (a + 0))
:= by intro a Na; apply natEq Na; exact addNatZeroEqNat Na

instance natAddNatZero_inst 
{P : Sort u} {T : Type v} {L : Logic P}
[N : IsNat P T] [Q : LEq P T] [A : Add T] [Z : Zero T]  
[NatEqNat L N Q] [AddNatZeroEqNat L N Q A Z] : NatAddNatZero L N A Z 
:= {natAddNatZero := natAddNatZero_proof}

instance natAddNatZero_spec {P : Sort u} {T : Type v}
{L : Logic P} [N : IsNat P T] [A : Add T] [Z : Zero T] [NatZero L N Z]
[K : NatAddNat L N A] : NatAddNatZero L N A Z 
:= {natAddNatZero := fun a Na => K.natAddNat a 0 Na nat0 }

-- nat (0 + a)

def natAddZeroNat_proof
{P : Sort u} {T : Type v} {L : Logic P}
[N : IsNat P T] [Q : LEq P T] [A : Add T] [Z : Zero T]  
[NatEqNat L N Q] [AddZeroNatEqNat L N Q A Z]
: (a : T) -> (L |- nat a) -> (L |- nat (0 + a))
:= by intro a Na; apply natEq Na; exact addZeroNatEqNat Na

instance natAddZeroNat_inst 
  {P : Sort u} {T : Type v} {L : Logic P}
  [N : IsNat P T] [Q : LEq P T] [A : Add T] [Z : Zero T]  
  [NatEqNat L N Q] [AddZeroNatEqNat L N Q A Z] : NatAddZeroNat L N A Z 
  := {natAddZeroNat := natAddZeroNat_proof}

instance natAddZeroNat_spec {P : Sort u} {T : Type v}
  {L : Logic P} [N : IsNat P T] [A : Add T] [Z : Zero T] [NatZero L N Z]
  [K : NatAddNat L N A] : NatAddZeroNat L N A Z 
  := {natAddZeroNat := fun a Na => K.natAddNat 0 a nat0 Na }

-- nat (a + b)

def natAddNat_proof 
{P : Sort u} {T : Type v} {L : Logic P}
[N : PNat P T] [Q : LEq P T] [A : Add T]
[NatInductionRight L N] 
[NatEqNat L N.toIsNat Q] 
[NatSuccNat L N.toIsNat N.toSucc]
[AddNatZeroEqNat L N.toIsNat Q A N.toZero]
[AddNatSuccEqSucc L N.toIsNat Q A N.toSucc]
: (a b : T) -> (L |- nat a) -> (L |- nat b) -> (L |- nat (a + b))
:= by
  refine natInductionRight ?f0 ?fS
  case f0 =>
    intro a Na
    exact natAddNatZero Na
  case fS =>
    intro a b Na Nb NAab
    have AaSb_eq_SAab := addNatSuccEqSucc Na Nb
    refine natEq ?_ AaSb_eq_SAab
    exact natS NAab

instance natAddNat_inst 
{P : Sort u} {T : Type v} {L : Logic P} 
[N : PNat P T] [Q : LEq P T] [A : Add T]
[NatInductionRight L N] [NatEqNat L N.toIsNat Q] [NatSuccNat L N.toIsNat N.toSucc]
[AddNatZeroEqNat L N.toIsNat Q A N.toZero] [AddNatSuccEqSucc L N.toIsNat Q A N.toSucc]
: NatAddNat L N.toIsNat A := {natAddNat := natAddNat_proof}

--------------------------------------------------------------------------------
-- Special Cases
--------------------------------------------------------------------------------

-- 0 + 0 = 0

instance addZeroEqZero_spec_addNatZero
{P : Sort u} {T : Type v} {L : Logic P}
[N : IsNat P T] [Q : LEq P T] [A : Add T] [Z : Zero T] 
[NatZero L N Z] [AddNatZeroEqNat L N Q A Z]
: AddZeroEqZero L Q A Z
:= {addZeroEqZero := addNatZeroEqNat nat0}

instance addZeroEqZero_spec_addZeroNat
{P : Sort u} {T : Type v} {L : Logic P}
[N : IsNat P T] [Q : LEq P T] [A : Add T] [Z : Zero T] 
[NatZero L N Z] [AddZeroNatEqNat L N Q A Z]
: AddZeroEqZero L Q A Z
:= {addZeroEqZero := addZeroNatEqNat nat0}

-- a + 1 = S a

def addNatOneEqSucc_proof_natAdd
{P : Sort u} {T : Type v} {L : Logic P}
[N : IsNat P T] [Q : LEq P T] [A : Add T] [Z : Zero T] [N1 : One T] [NS : Succ T] 
[NatZero L N Z]
[NatSuccNat L N NS]
[EqNatTrans L N Q]
[EqNatToEqSucc L N Q NS]
[NatOne L N N1]
[OneEqSuccZero L Q Z N1 NS]
[NatAddNat L N A]
[AddNatZeroEqNat L N Q A Z]
[AddNatSuccEqSucc L N Q A NS]
[EqNatAddNatLeft L N Q A]  
: (a : T) -> (L |- nat a) -> (L |- a + 1 = S a)
:= by
  intro a Na
  have NSa := natS Na
  have NS0 := natS (natZero L T)
  have NAa1 := natAdd Na nat1
  have NAa0 := natAdd Na nat0
  have NAaS0 := natAdd Na NS0
  have NSAa0 := natS NAa0
  refine eqNatTrans' NAaS0 NAa1 NSa ?Aa1_eq_AaS0 ?AaS0_eq_Sa
  exact eqNatAddNatLeft' Na nat1 NS0 oneEqSuccZero
  refine eqNatTrans' NSAa0 NAaS0 NSa ?AaS0_eq_SAa0 ?SAa0_eq_Sa
  exact addNatSuccEqSucc Na nat0
  apply eqNatToEqSucc NAa0 Na
  exact addNatZeroEqNat Na

instance addNatOneEqSucc_inst_natAdd
{P : Sort u} {T : Type v} {L : Logic P}
[N : IsNat P T] [Q : LEq P T] [A : Add T] [Z : Zero T] [N1 : One T] [NS : Succ T] 
[NatZero L N Z]
[NatSuccNat L N NS]
[EqNatTrans L N Q]
[EqNatToEqSucc L N Q NS]
[NatOne L N N1]
[OneEqSuccZero L Q Z N1 NS]
[NatAddNat L N A]
[AddNatZeroEqNat L N Q A Z]
[AddNatSuccEqSucc L N Q A NS]
[EqNatAddNatLeft L N Q A]  
: AddNatOneEqSucc L N Q A N1 NS
:= {addNatOneEqSucc := addNatOneEqSucc_proof_natAdd}

def addNatOneEqSucc_proof_natEq
{P : Sort u} {T : Type v} {L : Logic P}
[N : IsNat P T] [Q : LEq P T] [A : Add T] [Z : Zero T] [N1 : One T] [NS : Succ T] 
[NatZero L N Z]
[NatSuccNat L N NS]
[NatEqNat L N Q]
[EqNatTrans L N Q]
[EqNatToEqSucc L N Q NS]
[EqNatAddNatLeft L N Q A] 
[AddNatZeroEqNat L N Q A Z]
[AddNatSuccEqSucc L N Q A NS]
[OneEqSuccZero L Q Z N1 NS] 
: (a : T) -> (L |- nat a) -> (L |- a + 1 = S a)
:= by
  intro a Na
  have NSa := natS Na
  have NS0 := natS (natZero L T)
  have NAa0 := natAddNatZero Na
  apply eqTransNat (a + S 0) NSa
  exact eqNatAddNatLeft' Na nat1 NS0 oneEqSuccZero
  apply eqTransNat (S (a + 0)) NSa
  exact addNatSuccEqSucc Na nat0
  apply eqNatToEqSucc NAa0 Na
  exact addNatZeroEqNat Na

instance addNatOneEqSucc_inst_natEq
{P : Sort u} {T : Type v} {L : Logic P}
[N : IsNat P T] [Q : LEq P T] [A : Add T] [Z : Zero T] [N1 : One T] [NS : Succ T] 
[NatZero L N Z]
[NatSuccNat L N NS]
[NatEqNat L N Q]
[EqNatTrans L N Q]
[EqNatToEqSucc L N Q NS]
[EqNatAddNatLeft L N Q A] 
[AddNatZeroEqNat L N Q A Z]
[AddNatSuccEqSucc L N Q A NS]
[OneEqSuccZero L Q Z N1 NS] 
: AddNatOneEqSucc L N Q A N1 NS
:= {addNatOneEqSucc := addNatOneEqSucc_proof_natEq}

-- 1 + a = S a

def addOneNatEqSucc_proof_natAdd
{P : Sort u} {T : Type v} {L : Logic P}
[N : IsNat P T] [Q : LEq P T] [A : Add T] [Z : Zero T] [N1 : One T] [NS : Succ T] 
[NatZero L N Z]
[NatSuccNat L N NS]
[EqNatTrans L N Q]
[EqNatToEqSucc L N Q NS]
[NatOne L N N1]
[OneEqSuccZero L Q Z N1 NS]
[NatAddNat L N A]
[AddZeroNatEqNat L N Q A Z]
[AddSuccNatEqSucc L N Q A NS]
[EqNatAddNatRight L N Q A]  
: (a : T) -> (L |- nat a) -> (L |- 1 + a = S a)
:= by 
  intro a Na
  have NSa := natS Na
  have NS0 := natS (natZero L T)
  have NA1a := natAdd nat1 Na
  have NA0a := natAdd nat0 Na
  have NAS0a := natAdd NS0 Na
  have NSA0a := natS NA0a
  refine eqNatTrans' NAS0a NA1a NSa ?A1a_eq_AS0a ?AS0a_eq_Sa
  exact eqNatAddNatRight' Na nat1 NS0 oneEqSuccZero
  refine eqNatTrans' NSA0a NAS0a NSa ?AS0a_eq_SAa0 ?SA0a_eq_Sa
  exact addSuccNatEqSucc nat0 Na 
  apply eqNatToEqSucc NA0a Na
  exact addZeroNatEqNat Na

instance addOneNatEqSucc_inst_natAdd
{P : Sort u} {T : Type v} {L : Logic P}
[N : IsNat P T] [Q : LEq P T] [A : Add T] [Z : Zero T] [N1 : One T] [NS : Succ T] 
[NatZero L N Z]
[NatSuccNat L N NS]
[EqNatTrans L N Q]
[EqNatToEqSucc L N Q NS]
[NatOne L N N1]
[OneEqSuccZero L Q Z N1 NS]
[NatAddNat L N A]
[AddZeroNatEqNat L N Q A Z]
[AddSuccNatEqSucc L N Q A NS]
[EqNatAddNatRight L N Q A]
: AddOneNatEqSucc L N Q A N1 NS
:= {addOneNatEqSucc := addOneNatEqSucc_proof_natAdd}

--------------------------------------------------------------------------------
-- Commuted Axioms
--------------------------------------------------------------------------------

-- 0 + a = 0

def addZeroNatEqNat_proof
{P : Sort u} {T : Type v} {L : Logic P} 
[N : PNat P T] [Q : LEq P T] [A : Add T] 
[NatInduction L N]
[NatZero L N.toIsNat N.toZero] 
[NatSuccNat L N.toIsNat N.toSucc]
[NatAddZeroNat L N.toIsNat A N.toZero]
[EqNatTrans L N.toIsNat Q] 
[EqNatToEqSucc L N.toIsNat Q N.toSucc]  
[AddNatSuccEqSucc L N.toIsNat Q A N.toSucc]
[AddZeroEqZero L Q A N.toZero]
: (a : T) -> (L |- nat a) -> (L |- 0 + a = a)
:= by
  refine natInduction addZeroEqZero ?fS
  case fS => 
    intro a Na A0a_eq_a
    have NSa := natS Na
    have NA0a := natAddZeroNat Na
    apply eqNatTrans' (natS NA0a) 
      (natAddZeroNat NSa) NSa
    exact addNatSuccEqSucc nat0 Na
    exact eqNatToEqSucc NA0a Na A0a_eq_a

instance addZeroNatEqNat_inst 
{P : Sort u} {T : Type v} {L : Logic P} 
[N : PNat P T] [Q : LEq P T] [A : Add T] 
[NatInduction L N]
[NatZero L N.toIsNat N.toZero] 
[NatSuccNat L N.toIsNat N.toSucc]
[NatAddZeroNat L N.toIsNat A N.toZero]
[EqNatTrans L N.toIsNat Q] 
[EqNatToEqSucc L N.toIsNat Q N.toSucc]  
[AddNatSuccEqSucc L N.toIsNat Q A N.toSucc]
[AddZeroEqZero L Q A N.toZero]
: AddZeroNatEqNat L N.toIsNat Q A N.toZero
:= {addZeroNatEqNat := addZeroNatEqNat_proof}

-- S a + b = S (a + b)

def addSuccNatEqSucc_proof
{P : Sort u} {T : Type v} {L : Logic P} 
[N : PNat P T] [Q : LEq P T] [A : Add T]
[NatInductionRight L N]
[NatSuccNat L N.toIsNat N.toSucc]
[EqNatTrans L N.toIsNat Q]
[EqNatLeftEuc L N.toIsNat Q]
[EqNatToEqSucc L N.toIsNat Q N.toSucc]  
[NatAddNat L N.toIsNat A]
[NatAddNatZero L N.toIsNat A N.toZero]
[AddNatZeroEqNat L N.toIsNat Q A N.toZero]
[AddNatSuccEqSucc L N.toIsNat Q A N.toSucc]
: (a b : T) -> (L |- nat a) -> (L |- nat b) -> (L |- S a + b = S (a + b))
:= by
  refine natInductionRight ?f0 ?fS
  case f0 => 
    intro a Na
    have NSa := natS Na
    have NAa0 := natAddNatZero Na
    apply eqNatLeftEuc NSa 
      (natAddNatZero NSa) (natS NAa0)
    exact addNatZeroEqNat (natS Na)
    apply eqNatToEqSucc NAa0 Na 
    exact addNatZeroEqNat Na
  case fS =>
    intro a b Na Nb ASab_eq_SAab
    have NSa := natS Na; have NSb := natS Nb
    have NAaSb := natAdd Na NSb; have NSAaSb := natS NAaSb
    have NASaSb := natAdd NSa NSb
    have NAab := natAdd Na Nb; have NSAab := natS NAab; have NSSAab := natS NSAab
    have NASab := natAdd NSa Nb; have NSASab := natS NASab; 
    have AaSb_eq_SAab := addNatSuccEqSucc Na Nb
    have ASaSb_eq_SASab := addNatSuccEqSucc NSa Nb
    have SASab_eq_SSAab := eqNatToEqSucc NASab NSAab ASab_eq_SAab
    have ASaSb_eq_SSAab := eqNatTrans' NSASab NASaSb NSSAab 
      ASaSb_eq_SASab SASab_eq_SSAab
    have SAaSb_eq_SSAab := eqNatToEqSucc NAaSb NSAab AaSb_eq_SAab
    exact eqNatLeftEuc NSSAab NASaSb NSAaSb ASaSb_eq_SSAab SAaSb_eq_SSAab

instance addSuccNatEqSucc_inst {P : Sort u} {T : Type v} {L : Logic P} 
[N : PNat P T] [Q : LEq P T] [A : Add T]
[NatInductionRight L N]
[NatSuccNat L N.toIsNat N.toSucc]
[EqNatTrans L N.toIsNat Q]
[EqNatLeftEuc L N.toIsNat Q]
[EqNatToEqSucc L N.toIsNat Q N.toSucc]  
[NatAddNat L N.toIsNat A]
[NatAddNatZero L N.toIsNat A N.toZero]
[AddNatZeroEqNat L N.toIsNat Q A N.toZero]
[AddNatSuccEqSucc L N.toIsNat Q A N.toSucc]
: AddSuccNatEqSucc L N.toIsNat Q A N.toSucc
:= {addSuccNatEqSucc := addSuccNatEqSucc_proof} 

--------------------------------------------------------------------------------
-- Commutativity
--------------------------------------------------------------------------------

-- 0 + a = a + 0

def addNatZeroComm_proof
{P : Sort u} {T : Type v} {L : Logic P} 
[N : IsNat P T] [Q : LEq P T] [A : Add T] [Z : Zero T]
[EqNatLeftEuc L N Q]
[NatAddNatZero L N A Z]
[NatAddZeroNat L N A Z]
[AddNatZeroEqNat L N Q A Z]
[AddZeroNatEqNat L N Q A Z]
: (a : T) -> (L |- nat a) -> (L |- a + 0 = 0 + a)
:= by
  intro a Na; apply eqNatLeftEuc Na
  exact natAddNatZero Na; exact natAddZeroNat Na
  exact addNatZeroEqNat Na; exact addZeroNatEqNat Na 

instance addNatZeroComm_inst 
{P : Sort u} {T : Type v} {L : Logic P} 
[N : IsNat P T] [Q : LEq P T] [A : Add T] [Z : Zero T]
[EqNatLeftEuc L N Q] [NatAddNatZero L N A Z] [NatAddZeroNat L N A Z]
[AddNatZeroEqNat L N Q A Z] [AddZeroNatEqNat L N Q A Z]
: AddNatZeroComm L N Q A Z 
:= {addNatZeroComm := addNatZeroComm_proof}

instance addNatZeroComm_inst_natAdd
{P : Sort u} {T : Type v} {L : Logic P} 
[N : IsNat P T] [Q : LEq P T] [A : Add T] [Z : Zero T]
[NatZero L N Z] [NatAddNat L N A] [EqNatLeftEuc L N Q]
[AddNatZeroEqNat L N Q A Z] [AddZeroNatEqNat L N Q A Z]
: AddNatZeroComm L N Q A Z 
:= {addNatZeroComm := addNatZeroComm_proof}

def addNatZeroComm_proof_leftEucNat
{P : Sort u} {T : Type v} {L : Logic P} 
[N : IsNat P T] [Q : LEq P T] [A : Add T] [Z : Zero T]
[EqLeftEucNat L N Q]
[AddNatZeroEqNat L N Q A Z]
[AddZeroNatEqNat L N Q A Z]
: (a : T) -> (L |- nat a) -> (L |- a + 0 = 0 + a)
:= by
  intro a Na; apply eqLeftEucNat Na
  exact addNatZeroEqNat Na; exact addZeroNatEqNat Na 

instance addNatZeroComm_inst_leftEucNat
{P : Sort u} {T : Type v} {L : Logic P} 
[N : IsNat P T] [Q : LEq P T] [A : Add T] [Z : Zero T]
[EqLeftEucNat L N Q] [AddNatZeroEqNat L N Q A Z] [AddZeroNatEqNat L N Q A Z]
: AddNatZeroComm L N Q A Z 
:= {addNatZeroComm := addNatZeroComm_proof_leftEucNat}

-- a + b = b + a

def addNatComm_proof 
{P : Sort u} {T : Type v} {L : Logic P} 
[N : PNat P T] [Q : LEq P T] [A : Add T]
[NatInductionRight L N]
[NatSuccNat L N.toIsNat N.toSucc]
[EqNatLeftEuc L N.toIsNat Q]
[EqNatToEqSucc L N.toIsNat Q N.toSucc]  
[NatAddNat L N.toIsNat A]
[AddNatZeroComm L N.toIsNat Q A N.toZero]
[AddSuccNatEqSucc L N.toIsNat Q A N.toSucc]
[AddNatSuccEqSucc L N.toIsNat Q A N.toSucc]
: (a b : T) -> (L |- nat a) -> (L |- nat b) -> (L |- a + b = b + a)
:= by
  refine natInductionRight ?f0 ?fS
  case f0 =>
    intro a Na
    exact addNatZeroComm Na
  case fS =>
    intro a b Na Nb Aab_eq_Aba
    have NSb := natS Nb
    have NAab := natAdd Na Nb; have NSAab := natS NAab;
    have NAba := natAdd Nb Na; have NSAba := natS NAba
    have NASba := natAdd NSb Na; have NASab := natAdd Na NSb
    apply eqNatLeftEuc NSAab NASab NASba
    exact addNatSuccEqSucc Na Nb
    apply eqNatLeftEuc NSAba NASba NSAab
    exact addSuccNatEqSucc Nb Na
    apply eqNatToEqSucc NAab NAba 
    exact Aab_eq_Aba

instance addNatComm_inst 
{P : Sort u} {T : Type v} {L : Logic P} 
[N : PNat P T] [Q : LEq P T] [A : Add T]
[NatInductionRight L N]
[NatSuccNat L N.toIsNat N.toSucc]
[EqNatLeftEuc L N.toIsNat Q]
[EqNatToEqSucc L N.toIsNat Q N.toSucc]  
[NatAddNat L N.toIsNat A]
[AddNatZeroComm L N.toIsNat Q A N.toZero]
[AddSuccNatEqSucc L N.toIsNat Q A N.toSucc]
[AddNatSuccEqSucc L N.toIsNat Q A N.toSucc]
: AddNatComm L N.toIsNat Q A 
:= {addNatComm := addNatComm_proof}

instance addNatComm_inst' 
{P : Sort u} {T : Type v} {L : Logic P} 
[N : PNat P T] [Q : LEq P T] [A : Add T] [FaN : MForallNat L N.toIsNat]
[NatInduction L N]
[NatZero L N.toIsNat N.toZero]
[NatSuccNat L N.toIsNat N.toSucc]
[NatAddNat L N.toIsNat A]  
[EqNatSymm L N.toIsNat Q]
[EqNatTrans L N.toIsNat Q]
[EqNatToEqSucc L N.toIsNat Q N.toSucc]
[AddNatZeroEqNat L N.toIsNat Q A N.toZero]
[AddNatSuccEqSucc L N.toIsNat Q A N.toSucc]
: AddNatComm L N.toIsNat Q A 
:= {addNatComm := addNatComm_proof}

--------------------------------------------------------------------------------
-- Associativity
-- (a + b) + c = a + (b + c)
--------------------------------------------------------------------------------

def addNatAssoc_proof 
{P : Sort u} {T : Type v} {L : Logic P} 
[N : PNat P T] [Q : LEq P T] [A : Add T]
[NatInductionRight3 L N]
[NatSuccNat L N.toIsNat N.toSucc]
[EqNatTrans L N.toIsNat Q] 
[EqNatLeftEuc L N.toIsNat Q]
[EqNatToEqSucc L N.toIsNat Q N.toSucc]
[EqNatAddNatLeft L N.toIsNat Q A]
[NatAddNat L N.toIsNat A]
[NatAddNatZero L N.toIsNat A N.toZero]
[AddNatZeroEqNat L N.toIsNat Q A N.toZero]
[AddNatSuccEqSucc L N.toIsNat Q A N.toSucc]
: (a b c : T) -> 
  (L |- nat a) -> (L |- nat b) -> (L |- nat c) ->
  (L |- (a + b) + c = a + (b + c))
:= by
  refine natInductionRight3 ?f0 ?fS
  case f0 =>
    intro a b Na Nb
    have NAab := natAdd Na Nb
    have NAb0 := natAddNatZero Nb
    refine eqNatLeftEuc NAab (natAddNatZero NAab) (natAdd Na NAb0) 
      ?AAab0_eq_Aab ?AaAb0_eq_Aab
    case AAab0_eq_Aab =>
      exact addNatZeroEqNat NAab
    case AaAb0_eq_Aab =>
      apply eqNatAddNatLeft' Na NAb0 Nb
      exact addNatZeroEqNat Nb
  case fS =>
    intro a b c Na Nb Nc AAabSc_eq_AaAbSc
    have NSc := natS Nc
    have NAab := natAdd Na Nb
    have NAbc := natAdd Nb Nc
    have NAbSc := natAdd Nb NSc
    have NAAabSc := natAdd NAab NSc
    have NAaAbSc := natAdd Na NAbSc
    have NAaAbc := natAdd Na NAbc
    have NSAaAbc := natS NAaAbc
    refine eqNatLeftEuc NSAaAbc
      NAAabSc NAaAbSc ?AAabSc_eq_SAaAbc ?AaAbSc_eq_SAaAbc
    case AAabSc_eq_SAaAbc =>
      have NAAabc := natAdd NAab Nc
      have NSAAabc := natS NAAabc
      apply eqNatTrans' NSAAabc NAAabSc NSAaAbc
      exact addNatSuccEqSucc NAab Nc
      apply eqNatToEqSucc NAAabc NAaAbc
      exact AAabSc_eq_AaAbSc
    case AaAbSc_eq_SAaAbc =>
      have NSAbc := natS NAbc
      have NAaSAbc := natAdd Na NSAbc
      apply eqNatTrans' NAaSAbc NAaAbSc NSAaAbc
      apply eqNatAddNatLeft' Na NAbSc NSAbc 
      exact addNatSuccEqSucc Nb Nc
      exact addNatSuccEqSucc Na NAbc

instance addNatAssoc_inst {P : Sort u} {T : Type v} {L : Logic P} 
{P : Sort u} {T : Type v} {L : Logic P} 
[N : PNat P T] [Q : LEq P T] [A : Add T]
[NatInductionRight3 L N]
[NatSuccNat L N.toIsNat N.toSucc]
[EqNatTrans L N.toIsNat Q] 
[EqNatLeftEuc L N.toIsNat Q]
[EqNatToEqSucc L N.toIsNat Q N.toSucc]
[EqNatAddNatLeft L N.toIsNat Q A]
[NatAddNat L N.toIsNat A]
[NatAddNatZero L N.toIsNat A N.toZero]
[AddNatZeroEqNat L N.toIsNat Q A N.toZero]
[AddNatSuccEqSucc L N.toIsNat Q A N.toSucc]
: AddNatAssoc L N.toIsNat Q A
:= {addNatAssoc := addNatAssoc_proof}

instance addNatAssoc_inst' 
{P : Sort u} {T : Type v} {L : Logic P} 
[N : PNat P T] [Q : LEq P T] [A : Add T] [FaN : MForallNat L N.toIsNat]
[NatInduction L N]
[NatZero L N.toIsNat N.toZero]
[NatSuccNat L N.toIsNat N.toSucc]
[NatAddNat L N.toIsNat A]  
[EqNatSymm L N.toIsNat Q]
[EqNatTrans L N.toIsNat Q]
[EqNatToEqSucc L N.toIsNat Q N.toSucc]
[EqNatAddNatLeft L N.toIsNat Q A]
[AddNatZeroEqNat L N.toIsNat Q A N.toZero]
[AddNatSuccEqSucc L N.toIsNat Q A N.toSucc]
: AddNatAssoc L N.toIsNat Q A
:= {addNatAssoc := addNatAssoc_proof}

end Gaea.Peano