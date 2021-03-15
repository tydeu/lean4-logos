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

def natCases 
{P : Sort u} {T : Type v} {L : Logic P} [N : Nat P T] [NatInduction L N]
: (f : T -> P) -> 
  (L |- f 0) -> ((n : T) -> (L |- nat n) -> (L |- f (S n))) -> 
    ((n : T) -> (L |- nat n) -> (L |- f n))
:= by
  intro f f0 fS n Nn
  have ih : (n : T) -> (L |- nat n) -> (L |- f n) -> (L |- f (S n)) := 
    fun n Nn fn => fS n Nn
  exact natInduction f0 ih n Nn

class EqNatLeftEuc {P : Sort u} {T : Type v} 
  (L : Logic P) (N : IsNat P T) (Q : LEq P T) :=
  (eqNatLeftEuc : (a b c : T) -> 
    (L |- nat a) -> (L |- nat b) -> (L |- nat c) -> 
    (L |- b = a) -> (L |- c = a) -> (L |- b = c))

def eqNatLeftEuc {P : Sort u} {T : Type v} 
  {L : Logic P} [N : IsNat P T] [Q : LEq P T]
  [C : EqNatLeftEuc L N Q] {a b c : T} := C.eqNatLeftEuc a b c 

def eqNatLeftEuc_proof {P : Sort u} {T : Type v} {L : Logic P}
[N : IsNat P T] [Q : LEq P T] [EqNatSymm L N Q] [EqNatTrans L N Q]
: (a b c : T) -> 
    (L |- nat a) -> (L |- nat b) -> (L |- nat c) -> 
    (L |- b = a) -> (L |- c = a) -> (L |- b = c)
:= by
  intro a b c Na Nb Nc Qba Qca
  have Qac := eqNatSymm Nc Na Qca
  exact eqNatTrans Nb Na Nc Qba Qac

instance eqNatLeftEuc_inst {P : Sort u} {T : Type v} {L : Logic P}
  [N : IsNat P T] [Q : LEq P T] [EqNatSymm L N Q] [EqNatTrans L N Q]
  : EqNatLeftEuc L N Q := {eqNatLeftEuc := eqNatLeftEuc_proof}

--------------------------------------------------------------------------------
-- Theorems related to Peano Addition being closed over the Naturals
--------------------------------------------------------------------------------

class NatAddNatZero {P : Sort u} {T : Type v} 
  (L : Logic P) (N : IsNat P T) (A : Add T) (Z : Zero T) :=
  (natAddNatZero : (a : T) -> (L |- nat a) -> (L |- nat (a + 0)))

def natAddNatZero {P : Sort u} {T : Type v} 
  {L : Logic P} [N : IsNat P T] [A : Add T] [Z : Zero T]
  [C : NatAddNatZero L N A Z] {a : T} := C.natAddNatZero a

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

class NatAddZeroNat {P : Sort u} {T : Type v} 
  (L : Logic P) (N : IsNat P T) (A : Add T) (Z : Zero T) :=
  (natAddZeroNat : (a : T) -> (L |- nat a) -> (L |- nat (0 + a)))

def natAddZeroNat {P : Sort u} {T : Type v} 
  {L : Logic P} [N : IsNat P T] [A : Add T] [Z : Zero T]
  [C : NatAddZeroNat L N A Z] {a : T} := C.natAddZeroNat a 

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

-- Proofs related to Peano Addition being closed over the Naturals

class NatAddNat {P : Sort u} {T : Type v}
  (L : Logic P) (N : IsNat P T) (A : Add T) :=
  (natAddNat : (a b : T) -> (L |- nat a) -> (L |- nat b) -> (L |- nat (a + b)))

def natAddNat {P : Sort u} {T : Type v}
  {L : Logic P} [N : IsNat P T] [A : Add T] [C : NatAddNat L N A]
  {a b : T} := C.natAddNat a b

def natAdd {P : Sort u} {T : Type v}
  {L : Logic P} [N : IsNat P T] [A : Add T] [C : NatAddNat L N A]
  {a b : T} := C.natAddNat a b

instance natAddNatZero_spec {P : Sort u} {T : Type v}
  {L : Logic P} [N : IsNat P T] [A : Add T] [Z : Zero T] [NatZero L N Z]
  [C : NatAddNat L N A] : NatAddNatZero L N A Z 
  := {natAddNatZero := fun a Na => C.natAddNat a 0 Na nat0 }

instance natAddZeroNat_spec {P : Sort u} {T : Type v}
  {L : Logic P} [N : IsNat P T] [A : Add T] [Z : Zero T] [NatZero L N Z]
  [C : NatAddNat L N A] : NatAddZeroNat L N A Z 
  := {natAddZeroNat := fun a Na => C.natAddNat 0 a nat0 Na }

-- Uses standard (predicate) induction 
def natAddNat_induct {P : Sort u} {T : Type v} {L : Logic P}
[N : Nat P T] [Q : LEq P T] [A : PAdd L N Q] [Fa : MForall L T] [If : MIf L]
[NatEqNat L N.toIsNat Q] [NatSuccNat L N.toIsNat N.toSucc] [NatInduction L N]
: (b : T) -> (L |- nat b) -> (L |- forall (a : T) => nat a -> nat (a + b))
:= by
  refine natInduction ?f0 ?fS
  apply forallNatIntro; intro a Na 
  exact natAddNatZero Na
  intro a Na p_Nn_to_NAna
  apply forallNatIntro; intro b Nb
  have AbSa_eq_SAba := addNatSuccEqSucc Nb Na
  have NAba := forallNatElim p_Nn_to_NAna Nb 
  exact natEq (natS NAba) AbSa_eq_SAba

def natAddNat_proof {P : Sort u} {T : Type v} {L : Logic P} 
[N : Nat P T] [Q : LEq P T] [A : PAdd L N Q] [Fa : MForall L T] [If : MIf L]
[NatEqNat L N.toIsNat Q] [NatSuccNat L N.toIsNat N.toSucc] [NatInduction L N]
: (a b : T) -> (L |- nat a) -> (L |- nat b) -> (L |- nat (a + b))
:= fun a b Na Nb => forallNatElim (natAddNat_induct b Nb) Na

instance natAddNat_inst {P : Sort u} {T : Type v} {L : Logic P} 
  [N : Nat P T] [Q : LEq P T] [A : PAdd L N Q] [Fa : MForall L T] [If : MIf L]
  [NatEqNat L N.toIsNat Q] [NatSuccNat L N.toIsNat N.toSucc] [NatInduction L N]
  : NatAddNat L N.toIsNat A.toAdd := {natAddNat := natAddNat_proof}

-- Uses schema induction
def natAddNat_schema_proof
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
  exact natAddNatZero Na
  -- Induction
  intro a Na ih b Nb
  have NAba := ih b Nb 
  have AbSa_eq_SAba := addNatSuccEqSucc Nb Na
  have NSAba := natS NAba
  exact natEq NSAba AbSa_eq_SAba
  exact Nn; exact Nm

instance natAddNat_schema_inst 
  {P : Sort u} {T : Type v} {L : Logic.{u,w} P}
  [N : Nat P T] [Q : LEq P T]  [A : PAdd L N Q]
  [NatEqNat L N.toIsNat Q] [NatSuccNat L N.toIsNat N.toSucc] 
  [NatInduction'.{u,v,(imax (v+1) w)} L N]
  : NatAddNat L N.toIsNat A.toAdd := {natAddNat := natAddNat_schema_proof}

--------------------------------------------------------------------------------
-- Theorems related to Peano Addition being commutative
--------------------------------------------------------------------------------

-- 9 + 9 = 9

def addZeroEqZero 
{P : Sort u} {T : Type v} {L : Logic P}
[Q : LEq P T] [A : Add T] [Z : Zero T] 
[N : IsNat P T] [NatZero L N Z] [AddNatZeroEqNat L N Q A Z]
: L |- 0 + 0 = (0 : T) 
:= addNatZeroEqNat nat0

-- 0 + a = 0

def addZeroNatEqNat_proof
{P : Sort u} {T : Type v} {L : Logic P} 
[N : Nat P T] [Q : LEq P T] [A : PAdd L N Q] 
[NatZero L N.toIsNat N.toZero] 
[NatSuccNat L N.toIsNat N.toSucc]
[EqNatTrans L N.toIsNat Q] 
[EqNatToEqSucc L N.toIsNat Q N.toSucc]  
[NatInduction L N]
[NatAddNat L N.toIsNat A.toAdd] 
: (a : T) -> (L |- nat a) -> (L |- 0 + a = a)
:= by
  refine natInduction addZeroEqZero ?fS
  case fS => 
    intro a Na A0a_eq_a
    have NSa := natS Na
    have NA0a := natAdd nat0 Na
    have A0Sa_eq_SA0a := addNatSuccEqSucc nat0 Na
    have AS0a_eq_Sa := eqNatToEqSucc NA0a Na A0a_eq_a
    exact eqNatTrans (natAdd nat0 NSa) (natS NA0a) NSa 
      A0Sa_eq_SA0a AS0a_eq_Sa

instance addZeroNatEqNat_inst 
  {P : Sort u} {T : Type v} {L : Logic P} 
  [N : Nat P T] [Q : LEq P T] [A : PAdd L N Q] 
  [NatZero L N.toIsNat N.toZero] [NatSuccNat L N.toIsNat N.toSucc]
  [EqNatTrans L N.toIsNat Q] [EqNatToEqSucc L N.toIsNat Q N.toSucc]  
  [NatInduction L N] [NatAddNat L N.toIsNat A.toAdd] 
  : AddZeroNatEqNat L N.toIsNat Q A.toAdd N.toZero
  := {addZeroNatEqNat := addZeroNatEqNat_proof}

class AddNatZeroComm {P : Sort u} {T : Type v} 
  (L : Logic P) (N : IsNat P T) (Q : LEq P T) (A : Add T) (Z : Zero T) :=
  (addNatZeroComm : (a : T) -> (L |- nat a) -> (L |- a + 0 = 0 + a))

def addNatZeroComm {P : Sort u} {T : Type v} 
  {L : Logic P} [N : IsNat P T] [Q : LEq P T] [A : Add T] [Z : Zero T]
  [C : AddNatZeroComm L N Q A Z] {a : T} := C.addNatZeroComm a

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

-- S a + b = S (a + b)

def addSuccNatEqSucc_induct
{P : Sort u} {T : Type v} {L : Logic P} 
[N : Nat P T] [Q : LEq P T] [A : PAdd L N Q] [MForall L T] [MIf L]
[NatZero L N.toIsNat N.toZero] 
[NatSuccNat L N.toIsNat N.toSucc]
[EqNatTrans L N.toIsNat Q]
[EqNatLeftEuc L N.toIsNat Q]
[EqNatToEqSucc L N.toIsNat Q N.toSucc]  
[NatInduction L N]
[NatAddNat L N.toIsNat A.toAdd] 
: (b : T) -> (L |- nat b) -> (L |- forall a => nat a -> S a + b = S (a + b))
:= by
  refine natInduction ?f0 ?fS
  case f0 => 
    apply forallNatIntro; intro a Na
    have NSa := natS Na; 
    have NAa0 := natAdd Na nat0
    apply eqNatLeftEuc NSa 
      (natAdd NSa nat0) (natS NAa0)
    exact addNatZeroEqNat (natS Na)
    have Aa0_eq_a := addNatZeroEqNat Na
    exact eqNatToEqSucc NAa0 Na Aa0_eq_a
  case fS =>
    intro b Nb p_ASnb_eq_Snb
    apply forallNatIntro; intro a Na
    have NSa := natS Na; have NSb := natS Nb
    have NAaSb := natAdd Na NSb; have NSAaSb := natS NAaSb
    have NASaSb := natAdd NSa NSb
    have NAab := natAdd Na Nb; have NSAab := natS NAab; have NSSAab := natS NSAab
    have NASab := natAdd NSa Nb; have NSASab := natS NASab; 
    have ASab_eq_SAab := forallNatElim p_ASnb_eq_Snb Na
    have AaSb_eq_SAab := addNatSuccEqSucc Na Nb
    have ASaSb_eq_SASab := addNatSuccEqSucc NSa Nb
    have SASab_eq_SSAab := eqNatToEqSucc NASab NSAab ASab_eq_SAab
    have ASaSb_eq_SSAab := eqNatTrans NASaSb NSASab NSSAab 
      ASaSb_eq_SASab SASab_eq_SSAab
    have SAaSb_eq_SSAab := eqNatToEqSucc NAaSb NSAab AaSb_eq_SAab
    exact eqNatLeftEuc NSSAab NASaSb NSAaSb ASaSb_eq_SSAab SAaSb_eq_SSAab

def addSuccNatEqSucc_proof
{P : Sort u} {T : Type v} {L : Logic P} 
[N : Nat P T] [Q : LEq P T] [A : PAdd L N Q] [MForall L T] [MIf L]
[NatInduction L N]
[NatZero L N.toIsNat N.toZero] 
[NatSuccNat L N.toIsNat N.toSucc]
[EqNatTrans L N.toIsNat Q]
[EqNatLeftEuc L N.toIsNat Q]
[EqNatToEqSucc L N.toIsNat Q N.toSucc]  
[NatAddNat L N.toIsNat A.toAdd] 
: (a b : T) -> (L |- nat a) -> (L |- nat b) -> (L |- S a + b = S (a + b))
:= by
  intro a b Na Nb
  have h := addSuccNatEqSucc_induct b Nb
  exact forallNatElim h Na

instance addSuccNatEqSucc_inst {P : Sort u} {T : Type v} {L : Logic P} 
  [N : Nat P T] [Q : LEq P T] [A : PAdd L N Q] [MForall L T] [MIf L]
  [NatZero L N.toIsNat N.toZero] [NatSuccNat L N.toIsNat N.toSucc]
  [EqNatTrans L N.toIsNat Q] [EqNatLeftEuc L N.toIsNat Q]
  [EqNatToEqSucc L N.toIsNat Q N.toSucc] [NatInduction L N]
  [NatAddNat L N.toIsNat A.toAdd]
  : AddSuccNatEqSucc L N.toIsNat Q A.toAdd N.toSucc
  := {addSuccNatEqSucc := addSuccNatEqSucc_proof} 

-- a + b = b + a

class AddNatComm {P : Sort u} {T : Type v} 
  (L : Logic P) (N : IsNat P T) (Q : LEq P T) (A : Add T) :=
  (addNatComm : (a b : T) -> (L |- nat a) -> (L |- nat b) -> (L |- a + b = b + a))

def addNatComm {P : Sort u} {T : Type v} 
  {L : Logic P} [N : IsNat P T] [Q : LEq P T] [A : Add T]
  [C : AddNatComm L N Q A] {a b : T} := C.addNatComm a b

def addNatComm_induct {P : Sort u} {T : Type v} {L : Logic P} 
[N : Nat P T] [Q : LEq P T] [A : PAdd L N Q] [Fa : MForall L T] [If : MIf L]
[NatInduction L N]
[NatZero L N.toIsNat N.toZero]
[NatSuccNat L N.toIsNat N.toSucc]
[EqNatLeftEuc L N.toIsNat Q]
[EqNatToEqSucc L N.toIsNat Q N.toSucc]  
[NatAddNat L N.toIsNat A.toAdd]
[AddZeroNatEqNat L N.toIsNat Q A.toAdd N.toZero]
[AddSuccNatEqSucc L N.toIsNat Q A.toAdd N.toSucc]
: (b : T) -> (L |- nat b) -> (L |- forall a => nat a -> a + b = b + a) 
:= by
  refine natInduction ?f0 ?fS
  case f0 =>
    apply forallNatIntro; intro a Na
    exact addNatZeroComm Na
  case fS =>
    intro b Nb p_Anb_comm
    apply forallNatIntro; intro a Na
    have NSb := natS Nb
    have NAab := natAdd Na Nb; have NSAab := natS NAab;
    have NAba := natAdd Nb Na; have NSAba := natS NAba
    have NASba := natAdd NSb Na; have NASab := natAdd Na NSb
    apply eqNatLeftEuc NSAab NASab NASba
    exact addNatSuccEqSucc Na Nb
    have Aab_comm := forallNatElim p_Anb_comm Na
    have SAab_comm := eqNatToEqSucc NAab NAba Aab_comm
    apply eqNatLeftEuc NSAba NASba NSAab
    exact addSuccNatEqSucc Nb Na
    have Aab_comm := forallNatElim p_Anb_comm Na
    exact eqNatToEqSucc NAab NAba Aab_comm

def addNatComm_proof {P : Sort u} {T : Type v} {L : Logic P} 
[N : Nat P T] [Q : LEq P T] [A : PAdd L N Q] [Fa : MForall L T] [If : MIf L]
[NatInduction L N]
[NatZero L N.toIsNat N.toZero]
[NatSuccNat L N.toIsNat N.toSucc]
[EqNatTrans L N.toIsNat Q]
[EqNatLeftEuc L N.toIsNat Q]
[EqNatToEqSucc L N.toIsNat Q N.toSucc]  
[NatAddNat L N.toIsNat A.toAdd]
: (a b : T) -> (L |- nat a) -> (L |- nat b) -> (L |- a + b = b + a) 
:= by
  intro a b Na Nb
  have h := addNatComm_induct b Nb
  exact forallNatElim h Na

instance addNatComm_inst 
  {P : Sort u} {T : Type v} {L : Logic P} 
  [N : Nat P T] [Q : LEq P T] [A : PAdd L N Q] 
  [Fa : MForall L T] [If : MIf L]
  [NatInduction L N]
  [NatZero L N.toIsNat N.toZero] [NatSuccNat L N.toIsNat N.toSucc]
  [EqNatTrans L N.toIsNat Q] [EqNatLeftEuc L N.toIsNat Q] 
  [EqNatToEqSucc L N.toIsNat Q N.toSucc] [NatAddNat L N.toIsNat A.toAdd]
  : AddNatComm L N.toIsNat Q A.toAdd 
  := {addNatComm := addNatComm_proof}

end Gaea.Peano