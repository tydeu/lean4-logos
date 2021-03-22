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

-- nat (0 + 0)

instance natAddZero_byAddZero_inst 
{P : Sort u} {T : Type v} {L : Logic P}
[N : IsNat P T] [Q : LEq P T] [A : Add T] [Z : Zero T]  
[NatZero L N Z] [NatEqNat L N Q] [AddZeroEqZero L Q A Z] 
: NatAddZero L N A Z 
:= {natAddZero := natEq nat0 addZeroEqZero}

instance natAddZero_byAddNatZero_inst 
{P : Sort u} {T : Type v} {L : Logic P}
[N : IsNat P T] [Q : LEq P T] [A : Add T] [Z : Zero T]  
[NatZero L N Z] [NatEqNat L N Q] [AddNatZeroEqNat L N Q A Z] 
: NatAddZero L N A Z 
:= {natAddZero := natEq nat0 (addNatZeroEqNat nat0)}

instance natAddZero_byAddZeroNat_inst 
{P : Sort u} {T : Type v} {L : Logic P}
[N : IsNat P T] [Q : LEq P T] [A : Add T] [Z : Zero T]  
[NatZero L N Z] [NatEqNat L N Q] [AddZeroNatEqNat L N Q A Z] 
: NatAddZero L N A Z 
:= {natAddZero := natEq nat0 (addZeroNatEqNat nat0)}

-- nat (a + 0)

def natAddNatZero_byNatInduction_proof
{P : Sort u} {T : Type v} {L : Logic P}
[N : PNat P T] [Q : LEq P T] [A : Add T]
[NatInduction L N]
[NatZero L N.toIsNat N.toZero]
[NatSuccNat L N.toIsNat N.toSucc]
[NatEqNat L N.toIsNat Q] 
[NatAddZero L N.toIsNat A N.toZero]
[AddSuccNatEqSucc L N.toIsNat Q A N.toSucc]
: (a : T) -> (L |- nat a) -> (L |- nat (a + 0))
:= by
  refine natInduction ?f0 ?fS
  case f0 =>
    exact natAddZero
  case fS =>
    intro a Na NAa0
    apply natEq (natS NAa0)
    exact addSuccNatEqSucc Na nat0

instance natAddNatZero_byNatInduction_inst 
{P : Sort u} {T : Type v} {L : Logic P} 
[N : PNat P T] [Q : LEq P T] [A : Add T]
[NatInduction L N]
[NatZero L N.toIsNat N.toZero]
[NatSuccNat L N.toIsNat N.toSucc]
[NatEqNat L N.toIsNat Q] 
[NatAddZero L N.toIsNat A N.toZero]
[AddSuccNatEqSucc L N.toIsNat Q A N.toSucc]
: NatAddNatZero L N.toIsNat A N.toZero 
:= {natAddNatZero := natAddNatZero_byNatInduction_proof}

instance natAddNatZero_byAddNatZero_inst 
{P : Sort u} {T : Type v} {L : Logic P}
[N : IsNat P T] [Q : LEq P T] [A : Add T] [Z : Zero T]  
[NatEqNat L N Q] [AddNatZeroEqNat L N Q A Z] : NatAddNatZero L N A Z 
:= {natAddNatZero := fun _ Na => natEq Na (addNatZeroEqNat Na)}

instance natAddNatZero_byNatAdd_inst {P : Sort u} {T : Type v}
{L : Logic P} [N : IsNat P T] [A : Add T] [Z : Zero T] 
[NatZero L N Z] [NatAddNat L N A] : NatAddNatZero L N A Z 
:= {natAddNatZero := fun _ Na => natAdd Na nat0}

-- nat (0 + a)

def natAddZeroNat_byNatInduction_proof
{P : Sort u} {T : Type v} {L : Logic P}
[N : PNat P T] [Q : LEq P T] [A : Add T]
[NatInduction L N]
[NatZero L N.toIsNat N.toZero]
[NatSuccNat L N.toIsNat N.toSucc]
[NatEqNat L N.toIsNat Q] 
[NatAddZero L N.toIsNat A N.toZero]
[AddNatSuccEqSucc L N.toIsNat Q A N.toSucc]
: (a : T) -> (L |- nat a) -> (L |- nat (0 + a))
:= by
  refine natInduction ?f0 ?fS
  case f0 =>
    exact natAddZero
  case fS =>
    intro a Na NA0a
    apply natEq (natS NA0a)
    exact addNatSuccEqSucc nat0 Na 

instance natAddZeroNat_byNatInduction_inst 
{P : Sort u} {T : Type v} {L : Logic P} 
[N : PNat P T] [Q : LEq P T] [A : Add T]
[NatInduction L N]
[NatZero L N.toIsNat N.toZero]
[NatSuccNat L N.toIsNat N.toSucc]
[NatEqNat L N.toIsNat Q] 
[NatAddZero L N.toIsNat A N.toZero]
[AddNatSuccEqSucc L N.toIsNat Q A N.toSucc]
: NatAddZeroNat L N.toIsNat A N.toZero 
:= {natAddZeroNat := natAddZeroNat_byNatInduction_proof}

instance natAddZeroNat_byAddZeroNat_inst 
  {P : Sort u} {T : Type v} {L : Logic P}
  [N : IsNat P T] [Q : LEq P T] [A : Add T] [Z : Zero T]  
  [NatEqNat L N Q] [AddZeroNatEqNat L N Q A Z] : NatAddZeroNat L N A Z 
  := {natAddZeroNat := fun _ Na => natEq Na (addZeroNatEqNat Na)}

instance natAddZeroNat_byNatAdd_inst {P : Sort u} {T : Type v}
  {L : Logic P} [N : IsNat P T] [A : Add T] [Z : Zero T] 
  [NatZero L N Z] [K : NatAddNat L N A] : NatAddZeroNat L N A Z 
  := {natAddZeroNat := fun _ Na => natAdd nat0 Na}

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
    apply natEq (natS NAab)
    exact addNatSuccEqSucc Na Nb

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

instance addZeroEqZero_byAddNatZero_inst
{P : Sort u} {T : Type v} {L : Logic P}
[N : IsNat P T] [Q : LEq P T] [A : Add T] [Z : Zero T] 
[NatZero L N Z] [AddNatZeroEqNat L N Q A Z]
: AddZeroEqZero L Q A Z
:= {addZeroEqZero := addNatZeroEqNat nat0}

instance addZeroEqZero_byAddZeroNat_inst
{P : Sort u} {T : Type v} {L : Logic P}
[N : IsNat P T] [Q : LEq P T] [A : Add T] [Z : Zero T] 
[NatZero L N Z] [AddZeroNatEqNat L N Q A Z]
: AddZeroEqZero L Q A Z
:= {addZeroEqZero := addZeroNatEqNat nat0}

-- a + 1 = S a

def addNatOneEqSucc_byNatAdd_proof
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

instance addNatOneEqSucc_byNatAdd_inst
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
:= {addNatOneEqSucc := addNatOneEqSucc_byNatAdd_proof}

def addNatOneEqSucc_byNatEq_proof
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
  apply eqNatAddNatLeft' Na nat1 NS0 
  exact oneEqSuccZero
  apply eqTransNat (S (a + 0)) NSa
  exact addNatSuccEqSucc Na nat0
  apply eqNatToEqSucc NAa0 Na
  exact addNatZeroEqNat Na

instance addNatOneEqSucc_byNatEq_inst
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
:= {addNatOneEqSucc := addNatOneEqSucc_byNatEq_proof}

-- 1 + a = S a

def addOneNatEqSucc_byNatAdd_proof
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
  apply eqNatTrans' NAS0a NA1a NSa
  apply eqNatAddNatRight' Na nat1 NS0 
  exact oneEqSuccZero
  apply eqNatTrans' NSA0a NAS0a NSa
  exact addSuccNatEqSucc nat0 Na 
  apply eqNatToEqSucc NA0a Na
  exact addZeroNatEqNat Na

instance addOneNatEqSucc_byNatAdd_inst
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
:= {addOneNatEqSucc := addOneNatEqSucc_byNatAdd_proof}

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
    apply eqNatToEqSucc NA0a Na 
    exact A0a_eq_a

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

instance addNatZeroComm_byNatAdd_inst
{P : Sort u} {T : Type v} {L : Logic P} 
[N : IsNat P T] [Q : LEq P T] [A : Add T] [Z : Zero T]
[NatZero L N Z] [NatAddNat L N A] [EqNatLeftEuc L N Q]
[AddNatZeroEqNat L N Q A Z] [AddZeroNatEqNat L N Q A Z]
: AddNatZeroComm L N Q A Z 
:= {addNatZeroComm := addNatZeroComm_proof}

def addNatZeroComm_byLeftEucNat_proof
{P : Sort u} {T : Type v} {L : Logic P} 
[N : IsNat P T] [Q : LEq P T] [A : Add T] [Z : Zero T]
[EqLeftEucNat L N Q]
[AddNatZeroEqNat L N Q A Z]
[AddZeroNatEqNat L N Q A Z]
: (a : T) -> (L |- nat a) -> (L |- a + 0 = 0 + a)
:= by
  intro a Na; apply eqLeftEucNat Na
  exact addNatZeroEqNat Na; exact addZeroNatEqNat Na 

instance addNatZeroComm_byLeftEucNat_inst
{P : Sort u} {T : Type v} {L : Logic P} 
[N : IsNat P T] [Q : LEq P T] [A : Add T] [Z : Zero T]
[EqLeftEucNat L N Q] [AddNatZeroEqNat L N Q A Z] [AddZeroNatEqNat L N Q A Z]
: AddNatZeroComm L N Q A Z 
:= {addNatZeroComm := addNatZeroComm_byLeftEucNat_proof}

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

instance addNatComm_byAddNatX_inst 
{P : Sort u} {T : Type v} {L : Logic P} 
[N : PNat P T] [Q : LEq P T] [A : Add T]
[NatInductionRight L N]
[NatZero L N.toIsNat N.toZero]
[NatSuccNat L N.toIsNat N.toSucc]
[NatAddNat L N.toIsNat A]  
[EqNatTrans L N.toIsNat Q]
[EqNatLeftEuc L N.toIsNat Q]
[EqNatToEqSucc L N.toIsNat Q N.toSucc]
[AddNatZeroEqNat L N.toIsNat Q A N.toZero]
[AddNatSuccEqSucc L N.toIsNat Q A N.toSucc]
: AddNatComm L N.toIsNat Q A 
:= {addNatComm := addNatComm_proof}

instance addNatComm_byPeano_inst 
{P : Sort u} {T : Type v} {L : Logic P} 
[N : PNat P T] [Q : LEq P T] [A : Add T] [FaN : MForallNat L N.toIsNat]
[NatInduction L N]
[NatZero L N.toIsNat N.toZero]
[NatSuccNat L N.toIsNat N.toSucc]
[NatEqNat L N.toIsNat Q]
[EqNatSymm L N.toIsNat Q]
[EqNatTrans L N.toIsNat Q]
[EqNatToEqSucc L N.toIsNat Q N.toSucc]
[AddNatZeroEqNat L N.toIsNat Q A N.toZero]
[AddNatSuccEqSucc L N.toIsNat Q A N.toSucc]
: AddNatComm L N.toIsNat Q A 
:= {addNatComm := addNatComm_proof}

--------------------------------------------------------------------------------
-- Substitutivity
--------------------------------------------------------------------------------

-- Left Addition
-- (a = b) -> (c + a = c + b)

def eqNatAddNatLeft_proof
{P : Sort u} {T : Type v} {L : Logic P} 
[N : PNat P T] [Q : LEq P T] [A : Add T] [If : MIf L]
[NatInductionRight3 L N]
[NatSuccNat L N.toIsNat N.toSucc]
[EqNatJoin L N.toIsNat Q] 
[EqNatToEqSucc L N.toIsNat Q N.toSucc]
[NatAddNat L N.toIsNat A]
[NatAddZeroNat L N.toIsNat A N.toZero]
[AddZeroNatEqNat L N.toIsNat Q A N.toZero]
[AddSuccNatEqSucc L N.toIsNat Q A N.toSucc]
: (a b c : T) -> (L |- nat a) -> (L |- nat b) -> (L |- nat c) ->
  (L |- a = b) -> (L |- c + a = c + b)
:= by
  intro a b c Na Nb Nc; refine ifElim ?_
  refine natInductionRight3 ?f0 ?fS a b c Na Nb Nc
    (f := fun a b c => (a = b : P) -> (c + a = c + b : P)) 
  case f0 =>
    intro a b Na Nb
    apply ifIntro; intro Qab
    exact eqNatJoin' Na Nb (natAddZeroNat Na) (natAddZeroNat Nb) Qab 
      (addZeroNatEqNat Na) (addZeroNatEqNat Nb)
  case fS =>
    intro a b c Na Nb Nc p_Qab_to_QAacAbc
    apply ifIntro; intro Qab
    have QAacAbc := ifElim p_Qab_to_QAacAbc Qab
    have NSc := natS Nc
    have NAca := natAdd Nc Na; have NAcb := natAdd Nc Nb
    apply eqNatJoin (natAdd NSc Na) (natAdd NSc Nb) (natS NAca) (natS NAcb)
      (addSuccNatEqSucc Nc Na) (addSuccNatEqSucc Nc Nb)
    apply eqNatToEqSucc NAca NAcb
    exact ifElim p_Qab_to_QAacAbc Qab

instance eqNatAddNatLeft_inst
{P : Sort u} {T : Type v} {L : Logic P} 
[N : PNat P T] [Q : LEq P T] [A : Add T] [If : MIf L]
[NatInductionRight3 L N]
[NatSuccNat L N.toIsNat N.toSucc]
[EqNatJoin L N.toIsNat Q] 
[EqNatToEqSucc L N.toIsNat Q N.toSucc]
[NatAddNat L N.toIsNat A]
[NatAddZeroNat L N.toIsNat A N.toZero]
[AddZeroNatEqNat L N.toIsNat Q A N.toZero]
[AddSuccNatEqSucc L N.toIsNat Q A N.toSucc]
: EqNatAddNatLeft L N.toIsNat Q A
:= {eqNatAddNatLeft := eqNatAddNatLeft_proof}

instance eqNatAddNatLeft_byAddNatX_inst
{P : Sort u} {T : Type v} {L : Logic P} 
[N : PNat P T] [Q : LEq P T] [A : Add T] [If : MIf L]
[NatInductionRight3 L N]
[NatZero L N.toIsNat N.toZero]
[NatSuccNat L N.toIsNat N.toSucc]
[EqNatTrans L N.toIsNat Q]
[EqNatLeftEuc L N.toIsNat Q]
[EqNatToEqSucc L N.toIsNat Q N.toSucc]
[NatAddNat L N.toIsNat A]
[AddNatZeroEqNat L N.toIsNat Q A N.toZero]
[AddNatSuccEqSucc L N.toIsNat Q A N.toSucc]
: EqNatAddNatLeft L N.toIsNat Q A
:= {eqNatAddNatLeft := eqNatAddNatLeft_proof}

instance eqNatAddNatLeft_byPeano_inst
{P : Sort u} {T : Type v} {L : Logic P} 
[N : PNat P T] [Q : LEq P T] [A : Add T] 
[FaN : MForallNat L N.toIsNat] [If : MIf L]
[NatInduction L N]
[NatZero L N.toIsNat N.toZero]
[NatSuccNat L N.toIsNat N.toSucc]
[NatEqNat L N.toIsNat Q]
[EqNatSymm L N.toIsNat Q]
[EqNatTrans L N.toIsNat Q]
[EqNatToEqSucc L N.toIsNat Q N.toSucc]
[AddNatZeroEqNat L N.toIsNat Q A N.toZero]
[AddNatSuccEqSucc L N.toIsNat Q A N.toSucc]
: EqNatAddNatLeft L N.toIsNat Q A
:= {eqNatAddNatLeft := eqNatAddNatLeft_proof}

-- Right Addition
-- (a = b) -> (a + c = b + c)

def eqNatAddNatRight_proof
{P : Sort u} {T : Type v} {L : Logic P} 
[N : PNat P T] [Q : LEq P T] [A : Add T] [If : MIf L]
[NatInductionRight3 L N]
[NatSuccNat L N.toIsNat N.toSucc]
[EqNatJoin L N.toIsNat Q] 
[EqNatToEqSucc L N.toIsNat Q N.toSucc]
[NatAddNat L N.toIsNat A]
[NatAddNatZero L N.toIsNat A N.toZero]
[AddNatZeroEqNat L N.toIsNat Q A N.toZero]
[AddNatSuccEqSucc L N.toIsNat Q A N.toSucc]
: (a b c : T) -> (L |- nat a) -> (L |- nat b) -> (L |- nat c) ->
  (L |- a = b) -> (L |- a + c = b + c)
:= by
  intro a b c Na Nb Nc; refine ifElim ?_
  refine natInductionRight3 ?f0 ?fS a b c Na Nb Nc
    (f := fun a b c => (a = b : P) -> (a + c = b + c : P)) 
  case f0 =>
    intro a b Na Nb
    apply ifIntro; intro Qab
    exact eqNatJoin' Na Nb (natAddNatZero Na) (natAddNatZero Nb) Qab 
      (addNatZeroEqNat Na) (addNatZeroEqNat Nb)
  case fS =>
    intro a b c Na Nb Nc p_Qab_to_QAacAbc
    apply ifIntro; intro Qab
    have QAacAbc := ifElim p_Qab_to_QAacAbc Qab
    have NSc := natS Nc
    have NAac := natAdd Na Nc; have NAbc := natAdd Nb Nc
    have NAaSc := natAdd Na NSc; have NAbSc := natAdd Nb NSc
    apply eqNatJoin NAaSc NAbSc (natS NAac) (natS NAbc)
      (addNatSuccEqSucc Na Nc) (addNatSuccEqSucc Nb Nc)
    apply eqNatToEqSucc NAac NAbc
    exact ifElim p_Qab_to_QAacAbc Qab

instance eqNatAddNatRight_inst {P : Sort u} {T : Type v} {L : Logic P} 
{P : Sort u} {T : Type v} {L : Logic P} 
[N : PNat P T] [Q : LEq P T] [A : Add T] [If : MIf L]
[NatInductionRight3 L N]
[NatSuccNat L N.toIsNat N.toSucc]
[EqNatJoin L N.toIsNat Q] 
[EqNatToEqSucc L N.toIsNat Q N.toSucc]
[NatAddNat L N.toIsNat A]
[NatAddNatZero L N.toIsNat A N.toZero]
[AddNatZeroEqNat L N.toIsNat Q A N.toZero]
[AddNatSuccEqSucc L N.toIsNat Q A N.toSucc]
: EqNatAddNatRight L N.toIsNat Q A
:= {eqNatAddNatRight := eqNatAddNatRight_proof}

instance eqNatAddNatRight_byPeano_inst
{P : Sort u} {T : Type v} {L : Logic P} 
[N : PNat P T] [Q : LEq P T] [A : Add T] 
[FaN : MForallNat L N.toIsNat] [If : MIf L]
[NatInduction L N]
[NatZero L N.toIsNat N.toZero]
[NatSuccNat L N.toIsNat N.toSucc]
[NatEqNat L N.toIsNat Q]
[EqNatSymm L N.toIsNat Q]
[EqNatTrans L N.toIsNat Q]
[EqNatToEqSucc L N.toIsNat Q N.toSucc]
[AddNatZeroEqNat L N.toIsNat Q A N.toZero]
[AddNatSuccEqSucc L N.toIsNat Q A N.toSucc]
: EqNatAddNatRight L N.toIsNat Q A
:= {eqNatAddNatRight := eqNatAddNatRight_proof}

--------------------------------------------------------------------------------
-- Associativity
--------------------------------------------------------------------------------

-- (a + b) + c = a + (b + c)

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

instance addNatAssoc_byAddNatX_inst 
{P : Sort u} {T : Type v} {L : Logic P} 
[N : PNat P T] [Q : LEq P T] [A : Add T] [FaN : MForallNat L N.toIsNat]
[NatInduction L N]
[NatZero L N.toIsNat N.toZero]
[NatSuccNat L N.toIsNat N.toSucc]
[NatAddNat L N.toIsNat A]  
[EqNatTrans L N.toIsNat Q]
[EqNatLeftEuc L N.toIsNat Q]
[EqNatToEqSucc L N.toIsNat Q N.toSucc]
[EqNatAddNatLeft L N.toIsNat Q A]
[AddNatZeroEqNat L N.toIsNat Q A N.toZero]
[AddNatSuccEqSucc L N.toIsNat Q A N.toSucc]
: AddNatAssoc L N.toIsNat Q A
:= {addNatAssoc := addNatAssoc_proof}

instance addNatAssoc_byPeano_inst 
{P : Sort u} {T : Type v} {L : Logic P} 
[N : PNat P T] [Q : LEq P T] [A : Add T] [FaN : MForallNat L N.toIsNat] [If : MIf L]
[NatInduction L N]
[NatZero L N.toIsNat N.toZero]
[NatSuccNat L N.toIsNat N.toSucc]
[NatEqNat L N.toIsNat Q]
[EqNatSymm L N.toIsNat Q]
[EqNatTrans L N.toIsNat Q] 
[EqNatToEqSucc L N.toIsNat Q N.toSucc]
[AddNatZeroEqNat L N.toIsNat Q A N.toZero]
[AddNatSuccEqSucc L N.toIsNat Q A N.toSucc]
: AddNatAssoc L N.toIsNat Q A
:= {addNatAssoc := addNatAssoc_proof}

-- a + (b + c) = (a + b) + c 

def addNatAssocRev_proof 
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
  (L |- a + (b + c) = (a + b) + c)
:= by
  refine natInductionRight3 ?f0 ?fS
  case f0 =>
    intro a b Na Nb
    have NAab := natAdd Na Nb
    have NAb0 := natAddNatZero Nb
    refine eqNatLeftEuc NAab (natAdd Na NAb0) (natAddNatZero NAab)
      ?AaAb0_eq_Aab ?AAab0_eq_Aab
    case AaAb0_eq_Aab =>
      apply eqNatAddNatLeft' Na NAb0 Nb
      exact addNatZeroEqNat Nb
    case AAab0_eq_Aab =>
      exact addNatZeroEqNat NAab
  case fS =>
    intro a b c Na Nb Nc AaAbSc_eq_AAabSc
    have NSc := natS Nc
    have NAab := natAdd Na Nb
    have NAbc := natAdd Nb Nc
    have NAbSc := natAdd Nb NSc
    have NAAabSc := natAdd NAab NSc
    have NAaAbSc := natAdd Na NAbSc
    have NAAabc := natAdd NAab Nc
    have NSAAabc := natS NAAabc
    refine eqNatLeftEuc NSAAabc
      NAaAbSc NAAabSc ?AaAbSc_eq_SAAabc ?AAabSc_eq_SAAabc
    case AaAbSc_eq_SAAabc =>
      have NSAbc := natS NAbc
      have NAaSAbc := natAdd Na NSAbc
      have NAaAbc := natAdd Na NAbc
      have NSAaAbc := natS NAaAbc
      apply eqNatTrans' NAaSAbc NAaAbSc NSAAabc
      apply eqNatAddNatLeft' Na NAbSc NSAbc 
      exact addNatSuccEqSucc Nb Nc
      apply eqNatTrans' NSAaAbc NAaSAbc NSAAabc
      exact addNatSuccEqSucc Na NAbc
      apply eqNatToEqSucc NAaAbc NAAabc
      exact AaAbSc_eq_AAabSc
    case AAabSc_eq_SAAabc =>
      exact addNatSuccEqSucc NAab Nc

instance addNatAssocRev_inst {P : Sort u} {T : Type v} {L : Logic P} 
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
: AddNatAssocRev L N.toIsNat Q A
:= {addNatAssocRev := addNatAssocRev_proof}

instance addNatAssocRev_byAddNatX_inst 
{P : Sort u} {T : Type v} {L : Logic P} 
[N : PNat P T] [Q : LEq P T] [A : Add T] [FaN : MForallNat L N.toIsNat]
[NatInduction L N]
[NatZero L N.toIsNat N.toZero]
[NatSuccNat L N.toIsNat N.toSucc]
[NatAddNat L N.toIsNat A]  
[EqNatTrans L N.toIsNat Q]
[EqNatLeftEuc L N.toIsNat Q]
[EqNatToEqSucc L N.toIsNat Q N.toSucc]
[EqNatAddNatLeft L N.toIsNat Q A]
[AddNatZeroEqNat L N.toIsNat Q A N.toZero]
[AddNatSuccEqSucc L N.toIsNat Q A N.toSucc]
: AddNatAssocRev L N.toIsNat Q A
:= {addNatAssocRev := addNatAssocRev_proof}

end Gaea.Peano