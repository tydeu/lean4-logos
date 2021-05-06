import Logos.Peano.Eq
import Logos.Peano.Num
import Logos.Peano.Succ
import Logos.Peano.Forall
import Logos.Peano.Induction
import Logos.Peano.Add.Rules

universes u v
variable {P : Sort u} {T : Sort v} 

open Logos.Notation
namespace Logos.Peano

variable 
  {L : Logic P}
  [N : SNat P T] [Z : Zero T] [O : One T] [S : Succ T]
  [A : SAdd T]
  [Q : SEq P T]

--------------------------------------------------------------------------------
-- Closure
--------------------------------------------------------------------------------

-- nat (0 + 0)

instance iNatAddZeroNyAddZero 
[N0 : NatZero L N Z] [NQ : NatEqNat L N Q] [A0 : AddZeroEqZero L Q A Z] 
: NatAddZero L N A Z 
:= {toFun := natEq nat0 addZeroEqZero}

instance iNatAddZeroByAddNatZero 
[N0 : NatZero L N Z] [NQ : NatEqNat L N Q] [An0 : AddNatZeroEqNat L N Q A Z] 
: NatAddZero L N A Z 
:= {toFun := natEq nat0 (addNatZeroEqNat nat0)}

instance iNatAddZeroByAddZeroNat 
[N0 : NatZero L N Z] [NQ : NatEqNat L N Q] [A0n : AddZeroNatEqNat L N Q A Z] 
: NatAddZero L N A Z 
:= {toFun := natEq nat0 (addZeroNatEqNat nat0)}

-- nat (a + 0)

def natAddNatZeroByInduction
(I   : NatInduction L N Z S)
(N0  : NatZero L N Z)
(NS  : NatSuccNat L N S)
(NQ  : NatEqNat L N Q)
(NA0 : NatAddZero L N A Z)
(ASn : AddSuccNatEqSucc L N Q A S)
: (a : T) -> (L |- nat a) -> (L |- nat (a + 0))
:= by
  refine natInduction ?f0 ?fS
  case f0 =>
    exact natAddZero
  case fS =>
    intro a Na NAa0
    apply natEq (natS NAa0)
    exact addSuccNatEqSucc Na nat0

instance iNatAddNatZeroByInduction 
[I   : NatInduction L N Z S]
[N0  : NatZero L N Z]
[NS  : NatSuccNat L N S]
[NQ  : NatEqNat L N Q] 
[NA0 : NatAddZero L N A Z]
[ASn : AddSuccNatEqSucc L N Q A S]
: NatAddNatZero L N A Z 
:= {toFun := natAddNatZeroByInduction I N0 NS NQ NA0 ASn}

instance iNatAddNatZeroByAddNatZero 
[NQ : NatEqNat L N Q] [An0 : AddNatZeroEqNat L N Q A Z] : NatAddNatZero L N A Z 
:= {toFun := fun _ Na => natEq Na (addNatZeroEqNat Na)}

instance iNatAddNatZeroByNatAdd
[N0 : NatZero L N Z] [NA : NatAddNat L N A] : NatAddNatZero L N A Z 
:= {toFun := fun _ Na => natAdd Na nat0}

-- nat (0 + a)

def natAddZeroNatByInduction
(I   : NatInduction L N Z S)
(N0  : NatZero L N Z)
(NS  : NatSuccNat L N S)
(NQ  : NatEqNat L N Q)
(NA0 : NatAddZero L N A Z)
(AnS : AddNatSuccEqSucc L N Q A S)
: (a : T) -> (L |- nat a) -> (L |- nat (0 + a))
:= by
  refine natInduction ?f0 ?fS
  case f0 =>
    exact natAddZero
  case fS =>
    intro a Na NA0a
    apply natEq (natS NA0a)
    exact addNatSuccEqSucc nat0 Na 

instance iNatAddZeroNatByInduction 
[I   : NatInduction L N Z S]
[N0  : NatZero L N Z]
[NS  : NatSuccNat L N S]
[NQ  : NatEqNat L N Q] 
[NA0 : NatAddZero L N A Z]
[An0 : AddNatSuccEqSucc L N Q A S]
: NatAddZeroNat L N A Z 
:= {toFun :=  natAddZeroNatByInduction I N0 NS NQ NA0 An0}

instance iNatAddZeroNatByAddZeroNat 
[N : SNat P T] [Q : SEq P T] [A : SAdd T] [Z : Zero T]  
[NQ : NatEqNat L N Q] [A0n : AddZeroNatEqNat L N Q A Z] : NatAddZeroNat L N A Z 
:= {toFun := fun _ Na => natEq Na (addZeroNatEqNat Na)}

instance iNatAddZeroNatByNatAdd 
[N : SNat P T] [A : SAdd T] [Z : Zero T] 
[N0 : NatZero L N Z] [NA : NatAddNat L N A] : NatAddZeroNat L N A Z 
:= {toFun := fun _ Na => natAdd nat0 Na}

-- nat (a + b)

def natAddNatByPeano 
(I   : NatInductionRight L N Z S)
(NQ  : NatEqNat L N Q)
(NS  : NatSuccNat L N S)
(An0 : AddNatZeroEqNat L N Q A Z)
(AnS : AddNatSuccEqSucc L N Q A S)
: (a b : T) -> (L |- nat a) -> (L |- nat b) -> (L |- nat (a + b))
:= by
  refine natInductionRight ?f0 ?fS
  case f0 =>
    intro a Na
    exact natAddNatZero Na
  case fS =>
    intro b Nb NAnb a Na 
    have NAab := NAnb a Na
    apply natEq (natS NAab)
    exact addNatSuccEqSucc Na Nb

instance iNatAddNatByPeano 
[FaN : LForallNat L N]
[I   : NatInduction L N Z S]
[NQ  : NatEqNat L N Q] 
[NS  : NatSuccNat L N S]
[An0 : AddNatZeroEqNat L N Q A Z] 
[AnS : AddNatSuccEqSucc L N Q A S]
: NatAddNat L N A := 
  {toFun := natAddNatByPeano iNatInductionRightByForallNat NQ NS An0 AnS}

--------------------------------------------------------------------------------
-- Basic Cases
--------------------------------------------------------------------------------

-- 0 + 0 = 0

instance iAddZeroEqZeroByAddNatZero
[N0 : NatZero L N Z] [An0 : AddNatZeroEqNat L N Q A Z]
: AddZeroEqZero L Q A Z
:= {toFun := addNatZeroEqNat nat0}

instance iAddZeroEqZeroByAddZeroNat
[N0 : NatZero L N Z] [A0n : AddZeroNatEqNat L N Q A Z]
: AddZeroEqZero L Q A Z
:= {toFun := addZeroNatEqNat nat0}

-- a + 0 = 0

def addNatZeroEqNatByNatAdd
(I    : NatInduction L N Z S)
(N0   : NatZero L N Z) 
(NS   : NatSuccNat L N S)
(NAn0 : NatAddNatZero L N A Z)
(QTr  : EqNatTrans L N Q) 
(QtS  : EqNatToEqSucc L N Q S)  
(A0   : AddZeroEqZero L Q A Z)
(ASn  : AddSuccNatEqSucc L N Q A S)
: (a : T) -> (L |- nat a) -> (L |- a + 0 = a)
:= by
  refine natInduction addZeroEqZero ?fS
  case fS => 
    intro a Na Aa0_eq_a
    have NSa := natS Na
    have NAa0 := natAddNatZero Na
    apply eqNatTrans' (natS NAa0) 
      (natAddNatZero NSa) NSa
    exact addSuccNatEqSucc Na nat0
    apply eqNatToEqSucc NAa0 Na 
    exact Aa0_eq_a

instance iAddNatZeroEqNatByNatAdd
[I    : NatInduction L N Z S]
[N0   : NatZero L N Z] 
[NS   : NatSuccNat L N S]
[NAn0 : NatAddNatZero L N A Z]
[QTr  : EqNatTrans L N Q] 
[QtS  : EqNatToEqSucc L N Q S]  
[A0   : AddZeroEqZero L Q A Z]
[ASn  : AddSuccNatEqSucc L N Q A S]
: AddNatZeroEqNat L N Q A Z
:= {toFun := addNatZeroEqNatByNatAdd I N0 NS NAn0 QTr QtS A0 ASn} 

instance iAddNatZeroEqNatByNatEq 
[I   : NatInduction L N Z S]
[N0  : NatZero L N Z] 
[NS  : NatSuccNat L N S]
[NQ  : NatEqNat L N Q]
[QTr : EqNatTrans L N Q] 
[QtS : EqNatToEqSucc L N Q S]  
[A0  : AddZeroEqZero L Q A Z]
[ASn : AddSuccNatEqSucc L N Q A S]
: AddNatZeroEqNat L N Q A Z :=
{toFun := 
  addNatZeroEqNatByNatAdd I N0 NS iNatAddNatZeroByInduction QTr QtS A0 ASn} 

-- 0 + a = 0

def addZeroNatEqNatByNatAdd
(I    : NatInduction L N Z S)
(N0   : NatZero L N Z) 
(NS   : NatSuccNat L N S)
(NA0n : NatAddZeroNat L N A Z)
(QTr  : EqNatTrans L N Q) 
(QtS  : EqNatToEqSucc L N Q S)  
(A0   : AddZeroEqZero L Q A Z)
(AnS  : AddNatSuccEqSucc L N Q A S)
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

instance iAddZeroNatEqNatByNatAdd
[I    : NatInduction L N Z S]
[N0   : NatZero L N Z] 
[NS   : NatSuccNat L N S]
[NA0n : NatAddZeroNat L N A Z]
[QTr  : EqNatTrans L N Q] 
[QtS  : EqNatToEqSucc L N Q S]  
[A0   : AddZeroEqZero L Q A Z]
[AnS  : AddNatSuccEqSucc L N Q A S]
: AddZeroNatEqNat L N Q A Z
:= {toFun := addZeroNatEqNatByNatAdd I N0 NS NA0n QTr QtS A0 AnS} 

instance iAddZeroNatEqNatByNatEq 
[I   : NatInduction L N Z S]
[N0  : NatZero L N Z] 
[NS  : NatSuccNat L N S]
[NQ  : NatEqNat L N Q]
[QTr : EqNatTrans L N Q] 
[QtS : EqNatToEqSucc L N Q S]  
[A0  : AddZeroEqZero L Q A Z]
[AnS : AddNatSuccEqSucc L N Q A S]
: AddZeroNatEqNat L N Q A Z := 
{toFun := 
  addZeroNatEqNatByNatAdd I N0 NS iNatAddZeroNatByInduction QTr QtS A0 AnS} 

instance iAddZeroNatEqNatByPeano 
[FaN : LForallNat L N]
[I   : NatInduction L N Z S]
[N0  : NatZero L N Z] 
[NS  : NatSuccNat L N S]
[NQ  : NatEqNat L N Q]
[QTr : EqNatTrans L N Q] 
[QtS : EqNatToEqSucc L N Q S]  
[An0 : AddNatZeroEqNat L N Q A Z]
[AnS : AddNatSuccEqSucc L N Q A S]
: AddZeroNatEqNat L N Q A Z := 
{toFun := 
  addZeroNatEqNatByNatAdd I N0 NS iNatAddZeroNatByNatAdd 
    QTr QtS iAddZeroEqZeroByAddNatZero AnS}

-- a + S b = S (a + b)

def addNatSuccEqSuccByNatAdd
(I    : NatInductionLeft L N Z S)
(NS   : NatSuccNat L N S)
(NA0n : NatAddZeroNat L N A Z)
(NA   : NatAddNat L N A)
(QTr  : EqNatTrans L N Q)
(QEL  : EqNatLeftEuc L N Q)
(QtS  : EqNatToEqSucc L N Q S)  
(A0n  : AddZeroNatEqNat L N Q A Z)
(ASn  : AddSuccNatEqSucc L N Q A S)
: (a b : T) -> (L |- nat a) -> (L |- nat b) -> (L |- a + S b = S (a + b))
:= by
  refine natInductionLeft ?f0 ?fS
  case f0 => 
    intro a Na
    have NSa := natS Na
    have NA0a := natAddZeroNat Na
    apply eqNatLeftEuc NSa 
      (natAddZeroNat NSa) (natS NA0a)
    exact addZeroNatEqNat NSa
    apply eqNatToEqSucc NA0a Na 
    exact addZeroNatEqNat Na
  case fS =>
    intro a Na AaSn_eq_SAan b Nb
    have NSa := natS Na
    have NSb := natS Nb
    have NASab := natAdd NSa Nb
    have NSASab := natS NASab
    have NASaSb := natAdd NSa NSb
    have NAab := natAdd Na Nb
    have NSAab := natS NAab
    have NSSAab := natS NSAab
    refine eqNatLeftEuc NSSAab NASaSb NSASab 
      ?ASSab_eq_SSAab ?SASab_eq_SSAab
    case ASSab_eq_SSAab =>
      have NAaSb := natAdd Na NSb
      have NSAaSb := natS NAaSb
      apply eqNatTrans' NSAaSb NASaSb NSSAab 
      exact addSuccNatEqSucc Na NSb 
      apply eqNatToEqSucc NAaSb NSAab 
      exact AaSn_eq_SAan b Nb
    case SASab_eq_SSAab =>
      apply eqNatToEqSucc NASab NSAab 
      exact addSuccNatEqSucc Na Nb

instance iAddNatSuccEqSuccByNatAdd 
[I   : NatInductionLeft L N Z S]
[NS  : NatSuccNat L N S]
[NA0n : NatAddZeroNat L N A Z]
[NA  : NatAddNat L N A]
[QTr : EqNatTrans L N Q]
[QEL : EqNatLeftEuc L N Q]
[QtS : EqNatToEqSucc L N Q S]  
[A0n : AddZeroNatEqNat L N Q A Z]
[ASn : AddSuccNatEqSucc L N Q A S]
: AddNatSuccEqSucc L N Q A S := 
{toFun := addNatSuccEqSuccByNatAdd I NS NA0n NA QTr QEL QtS A0n ASn}

-- S a + b = S (a + b)

def addSuccNatEqSuccByNatAdd
(I    : NatInductionRight L N Z S)
(NS   : NatSuccNat L N S)
(NAn0 : NatAddNatZero L N A Z)
(NA   : NatAddNat L N A)
(QTr  : EqNatTrans L N Q)
(QEL  : EqNatLeftEuc L N Q)
(QtS  : EqNatToEqSucc L N Q S)  
(An0  : AddNatZeroEqNat L N Q A Z)
(AnS  : AddNatSuccEqSucc L N Q A S)
: (a b : T) -> (L |- nat a) -> (L |- nat b) -> (L |- S a + b = S (a + b))
:= by
  refine natInductionRight ?f0 ?fS
  case f0 => 
    intro a Na
    have NSa := natS Na
    have NAa0 := natAddNatZero Na
    apply eqNatLeftEuc NSa 
      (natAddNatZero NSa) (natS NAa0)
    exact addNatZeroEqNat NSa
    apply eqNatToEqSucc NAa0 Na 
    exact addNatZeroEqNat Na
  case fS =>
    intro b Nb ASnb_eq_SAnb a Na
    have NSa := natS Na
    have NSb := natS Nb
    have NAaSb := natAdd Na NSb
    have NSAaSb := natS NAaSb
    have NASaSb := natAdd NSa NSb
    have NAab := natAdd Na Nb
    have NSAab := natS NAab
    have NSSAab := natS NSAab
    refine eqNatLeftEuc NSSAab NASaSb NSAaSb 
      ?ASaSb_eq_SSAab ?SAaSb_eq_SSAab
    case ASaSb_eq_SSAab =>
      have NASab := natAdd NSa Nb
      have NSASab := natS NASab
      apply eqNatTrans' NSASab NASaSb NSSAab 
      exact addNatSuccEqSucc NSa Nb 
      apply eqNatToEqSucc NASab NSAab 
      exact ASnb_eq_SAnb a Na
    case SAaSb_eq_SSAab =>
      apply eqNatToEqSucc NAaSb NSAab 
      exact addNatSuccEqSucc Na Nb

instance iAddSuccNatEqSuccByNatAdd 
[I   : NatInductionRight L N Z S]
[NS  : NatSuccNat L N S]
[NAn0 : NatAddNatZero L N A Z]
[NA  : NatAddNat L N A]
[QTr : EqNatTrans L N Q]
[QEL : EqNatLeftEuc L N Q]
[QtS : EqNatToEqSucc L N Q S]  
[An0 : AddNatZeroEqNat L N Q A Z]
[AnS : AddNatSuccEqSucc L N Q A S]
: AddSuccNatEqSucc L N Q A S := 
{toFun := addSuccNatEqSuccByNatAdd I NS NAn0 NA QTr QEL QtS An0 AnS} 

instance iAddSuccNatEqSuccByPeano 
[FaN : LForallNat L N]
[I   : NatInduction L N Z S]
[N0  : NatZero L N Z]
[NS  : NatSuccNat L N S]
[NQ  : NatEqNat L N Q]
[QSm : EqNatSymm L N Q]
[QTr : EqNatTrans L N Q]
[QtS : EqNatToEqSucc L N Q S]  
[An0 : AddNatZeroEqNat L N Q A Z]
[AnS : AddNatSuccEqSucc L N Q A S]
: AddSuccNatEqSucc L N Q A S := 
{toFun := 
  addSuccNatEqSuccByNatAdd iNatInductionRightByForallNat 
    NS iNatAddNatZeroByNatAdd iNatAddNatByPeano 
    QTr iEqNatLeftEucBySymmTransT QtS An0 AnS} 

--------------------------------------------------------------------------------
-- Commutativity
--------------------------------------------------------------------------------

-- 0 + a = a + 0

def addNatZeroCommByNatAddZero
(QEL  : EqNatLeftEuc L N Q)
(NAn0 : NatAddNatZero L N A Z)
(NA0n : NatAddZeroNat L N A Z)
(An0  : AddNatZeroEqNat L N Q A Z)
(A0n  : AddZeroNatEqNat L N Q A Z)
: (a : T) -> (L |- nat a) -> (L |- a + 0 = 0 + a)
:= by
  intro a Na; apply eqNatLeftEuc Na
  exact natAddNatZero Na; exact natAddZeroNat Na
  exact addNatZeroEqNat Na; exact addZeroNatEqNat Na 

instance iAddNatZeroCommByNatAddZero 
[QEL  : EqNatLeftEuc L N Q] 
[NAn0 : NatAddNatZero L N A Z] 
[NA0n : NatAddZeroNat L N A Z]
[An0  : AddNatZeroEqNat L N Q A Z] 
[A0n  : AddZeroNatEqNat L N Q A Z]
: AddNatZeroComm L N Q A Z 
:= {toFun := addNatZeroCommByNatAddZero QEL NAn0 NA0n An0 A0n}

instance iAddNatZeroCommByNatAdd
[QEL : EqNatLeftEuc L N Q]
[N0  : NatZero L N Z] 
[NA  : NatAddNat L N A] 
[An0 : AddNatZeroEqNat L N Q A Z] 
[A0n : AddZeroNatEqNat L N Q A Z]
: AddNatZeroComm L N Q A Z := 
{toFun := addNatZeroCommByNatAddZero QEL 
  iNatAddNatZeroByNatAdd iNatAddZeroNatByNatAdd An0 A0n}

instance iAddNatZeroCommByNatEq
[NQ  : NatEqNat L N Q]
[QSm : EqNatSymm L N Q]
[QTr : EqNatTrans L N Q] 
[An0 : AddNatZeroEqNat L N Q A Z] 
[A0n : AddZeroNatEqNat L N Q A Z]
: AddNatZeroComm L N Q A Z := 
{toFun := addNatZeroCommByNatAddZero iEqNatLeftEucBySymmTransT 
  iNatAddNatZeroByAddNatZero iNatAddZeroNatByAddZeroNat An0 A0n}

def addNatZeroCommByLeftEucNat
(QEL : EqLeftEucNat L N Q)
(An0 : AddNatZeroEqNat L N Q A Z)
(A0n : AddZeroNatEqNat L N Q A Z)
: (a : T) -> (L |- nat a) -> (L |- a + 0 = 0 + a)
:= by
  intro a Na; apply eqLeftEucNat Na
  exact addNatZeroEqNat Na; exact addZeroNatEqNat Na 

instance iAddNatZeroCommByLeftEucNat
[QEL : EqLeftEucNat L N Q] 
[An0 : AddNatZeroEqNat L N Q A Z] 
[A0n : AddZeroNatEqNat L N Q A Z]
: AddNatZeroComm L N Q A Z 
:= {toFun := addNatZeroCommByLeftEucNat QEL An0 A0n}

instance iAddNatZeroCommByPeano
[FaN : LForallNat L N] 
[I   : NatInduction L N Z S]
[N0  : NatZero L N Z] 
[NS  : NatSuccNat L N S]
[NQ  : NatEqNat L N Q]
[QSm : EqNatSymm L N Q]
[QTr : EqNatTrans L N Q] 
[QtS : EqNatToEqSucc L N Q S]  
[An0 : AddNatZeroEqNat L N Q A Z]
[AnS : AddNatSuccEqSucc L N Q A S]
: AddNatZeroComm L N Q A Z := 
{toFun := addNatZeroCommByLeftEucNat iEqLeftEucNatByNatEq 
  An0 iAddZeroNatEqNatByPeano}

-- a + b = b + a

def addNatCommProof
(I   : NatInductionRight L N Z S)
(NS  : NatSuccNat L N S)
(NA  : NatAddNat L N A)
(QEL : EqNatLeftEuc L N Q)
(QtS : EqNatToEqSucc L N Q S)  
(A0C : AddNatZeroComm L N Q A Z)
(ASn : AddSuccNatEqSucc L N Q A S)
(AnS : AddNatSuccEqSucc L N Q A S)
: (a b : T) -> (L |- nat a) -> (L |- nat b) -> (L |- a + b = b + a)
:= by
  refine natInductionRight ?f0 ?fS
  case f0 =>
    intro a Na
    exact addNatZeroComm Na
  case fS =>
    intro b Nb Anb_eq_Abn a Na
    have NSb := natS Nb
    have NAab := natAdd Na Nb; have NSAab := natS NAab;
    have NAba := natAdd Nb Na; have NSAba := natS NAba
    have NASba := natAdd NSb Na; have NASab := natAdd Na NSb
    apply eqNatLeftEuc NSAab NASab NASba
    exact addNatSuccEqSucc Na Nb
    apply eqNatLeftEuc NSAba NASba NSAab
    exact addSuccNatEqSucc Nb Na
    apply eqNatToEqSucc NAab NAba 
    exact Anb_eq_Abn a Na

instance iAddNatComm 
[I   : NatInductionRight L N Z S]
[NS  : NatSuccNat L N S]
[NA  : NatAddNat L N A]
[QEL : EqNatLeftEuc L N Q]
[QtS : EqNatToEqSucc L N Q S]  
[A0C : AddNatZeroComm L N Q A Z]
[ASn : AddSuccNatEqSucc L N Q A S]
[AnS : AddNatSuccEqSucc L N Q A S]
: AddNatComm L N Q A 
:= {toFun := addNatCommProof I NS NA QEL QtS A0C ASn AnS}

instance iAddNatCommByPeano 
[FaN : LForallNat L N]
[I   : NatInduction L N Z S]
[N0  : NatZero L N Z]
[NS  : NatSuccNat L N S]
[NQ  : NatEqNat L N Q]
[QSm : EqNatSymm L N Q]
[QTr : EqNatTrans L N Q]
[QtS : EqNatToEqSucc L N Q S]
[An0 : AddNatZeroEqNat L N Q A Z]
[AnS : AddNatSuccEqSucc L N Q A S]
: AddNatComm L N Q A := 
{toFun := 
  addNatCommProof iNatInductionRightByForallNat 
    NS iNatAddNatByPeano iEqNatLeftEucBySymmTransT QtS 
    iAddNatZeroCommByPeano iAddSuccNatEqSuccByPeano AnS}

--------------------------------------------------------------------------------
-- Substitutivity
--------------------------------------------------------------------------------

-- Left Addition
-- (a = b) -> (c + a = c + b)

def eqNatAddNatLeftProof
(I    : NatInductionRight3If L N Z S)
(NS   : NatSuccNat L N S)
(NA0n : NatAddZeroNat L N A Z)
(NA   : NatAddNat L N A)
(QJ   : EqNatJoin L N Q)
(QtS  : EqNatToEqSucc L N Q S)
(A0n  : AddZeroNatEqNat L N Q A Z)
(ASn  : AddSuccNatEqSucc L N Q A S)
: (a b c : T) -> (L |- nat a) -> (L |- nat b) -> (L |- nat c) ->
  (L |- a = b) -> (L |- c + a = c + b)
:= by
  refine natInductionRight3If ?f0 ?fS
  case f0 =>
    intro a b Na Nb Qab
    exact eqNatJoin' Na Nb (natAddZeroNat Na) (natAddZeroNat Nb) Qab 
      (addZeroNatEqNat Na) (addZeroNatEqNat Nb)
  case fS =>
    intro c Nc Qmn_to_QAcmAcn a b Na Nb Qab 
    have NSc := natS Nc; have NAca := natAdd Nc Na; have NAcb := natAdd Nc Nb
    apply eqNatJoin (natAdd NSc Na) (natAdd NSc Nb) (natS NAca) (natS NAcb)
      (addSuccNatEqSucc Nc Na) (addSuccNatEqSucc Nc Nb)
    apply eqNatToEqSucc NAca NAcb
    exact Qmn_to_QAcmAcn a b Na Nb Qab

instance iEqNatAddNatLeft
[FaN : LForallNat L N] [ent : LEnt L]
[I    : NatInductionRight3If L N Z S]
[NS   : NatSuccNat L N S]
[QJ   : EqNatJoin L N Q] 
[QtS  : EqNatToEqSucc L N Q S]
[NA   : NatAddNat L N A]
[NA0n : NatAddZeroNat L N A Z]
[A0n  : AddZeroNatEqNat L N Q A Z]
[ASn  : AddSuccNatEqSucc L N Q A S]
: EqNatAddNatLeft L N Q A
:= {toFun := eqNatAddNatLeftProof I NS NA0n NA QJ QtS A0n ASn}

instance iEqNatAddNatLeftByPeano
[FaN : LForallNat L N] [ent : LEnt L]
[I   : NatInduction L N Z S]
[N0  : NatZero L N Z]
[NS  : NatSuccNat L N S]
[NQ  : NatEqNat L N Q]
[QSm : EqNatSymm L N Q]
[QTr : EqNatTrans L N Q]
[QtS : EqNatToEqSucc L N Q S]
[An0 : AddNatZeroEqNat L N Q A Z]
[AnS : AddNatSuccEqSucc L N Q A S]
: EqNatAddNatLeft L N Q A := 
{toFun := 
  eqNatAddNatLeftProof iNatInductionRight3IfByForallNatIf 
    NS iNatAddZeroNatByNatAdd iNatAddNatByPeano iEqNatJoinBySymmTransT QtS 
    iAddZeroNatEqNatByPeano iAddSuccNatEqSuccByPeano}

-- Right Addition
-- (a = b) -> (a + c = b + c)

def eqNatAddNatRightProof
(I    : NatInductionRight3If L N Z S)
(NS   : NatSuccNat L N S)
(NAn0 : NatAddNatZero L N A Z)
(NA   : NatAddNat L N A)
(QJ   : EqNatJoin L N Q)
(QtS  : EqNatToEqSucc L N Q S)
(An0  : AddNatZeroEqNat L N Q A Z)
(AnS  : AddNatSuccEqSucc L N Q A S)
: (a b c : T) -> (L |- nat a) -> (L |- nat b) -> (L |- nat c) ->
  (L |- a = b) -> (L |- a + c = b + c)
:= by
  refine natInductionRight3If ?f0 ?fS
  case f0 =>
    intro a b Na Nb Qab
    exact eqNatJoin' Na Nb (natAddNatZero Na) (natAddNatZero Nb) Qab 
      (addNatZeroEqNat Na) (addNatZeroEqNat Nb)
  case fS =>
    intro c Nc Qmn_to_QAmcAnc a b Na Nb Qab 
    have NSc := natS Nc; have NAac := natAdd Na Nc; have NAbc := natAdd Nb Nc
    apply eqNatJoin (natAdd Na NSc) (natAdd Nb NSc) (natS NAac) (natS NAbc)
      (addNatSuccEqSucc Na Nc) (addNatSuccEqSucc Nb Nc)
    apply eqNatToEqSucc NAac NAbc
    exact Qmn_to_QAmcAnc a b Na Nb Qab

instance iEqNatAddNatRight 
[I    : NatInductionRight3If L N Z S]
[NS   : NatSuccNat L N S]
[QJ   : EqNatJoin L N Q] 
[QtS  : EqNatToEqSucc L N Q S]
[NA   : NatAddNat L N A]
[NAn0 : NatAddNatZero L N A Z]
[An0  : AddNatZeroEqNat L N Q A Z]
[AnS  : AddNatSuccEqSucc L N Q A S]
: EqNatAddNatRight L N Q A
:= {toFun := eqNatAddNatRightProof I NS NAn0 NA QJ QtS An0 AnS}

instance iEqNatAddNatRightByPeano
[FaN : LForallNat L N] [ent : LEnt L]
[I   : NatInduction L N Z S]
[N0  : NatZero L N Z]
[NS  : NatSuccNat L N S]
[NQ  : NatEqNat L N Q]
[QSm : EqNatSymm L N Q]
[QTr : EqNatTrans L N Q]
[QtS : EqNatToEqSucc L N Q S]
[An0 : AddNatZeroEqNat L N Q A Z]
[AnS : AddNatSuccEqSucc L N Q A S]
: EqNatAddNatRight L N Q A := 
{toFun := eqNatAddNatRightProof iNatInductionRight3IfByForallNatIf NS 
  iNatAddNatZeroByAddNatZero iNatAddNatByPeano iEqNatJoinBySymmTransT QtS An0 AnS} 

--------------------------------------------------------------------------------
-- Associativity
--------------------------------------------------------------------------------

-- (a + b) + c = a + (b + c)

def addNatAssocByAddNatX 
(I    : NatInductionRight3 L N Z S)
(NS   : NatSuccNat L N S)
(NAn0 : NatAddNatZero L N A Z)
(NA   : NatAddNat L N A)
(QTr  : EqNatTrans L N Q)
(QEL  : EqNatLeftEuc L N Q)
(QtS  : EqNatToEqSucc L N Q S)
(QAL  : EqNatAddNatLeft L N Q A)
(An0  : AddNatZeroEqNat L N Q A Z)
(AnS  : AddNatSuccEqSucc L N Q A S)
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
    intro c Nc AAmnSc_eq_AmAnSc a b Na Nb
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
      exact AAmnSc_eq_AmAnSc a b Na Nb
    case AaAbSc_eq_SAaAbc =>
      have NSAbc := natS NAbc
      have NAaSAbc := natAdd Na NSAbc
      apply eqNatTrans' NAaSAbc NAaAbSc NSAaAbc
      apply eqNatAddNatLeft' Na NAbSc NSAbc 
      exact addNatSuccEqSucc Nb Nc
      exact addNatSuccEqSucc Na NAbc

instance iAddNatAssocByAddNatX 
[I    : NatInductionRight3 L N Z S]
[NS   : NatSuccNat L N S]
[NAn0 : NatAddNatZero L N A Z]
[NA   : NatAddNat L N A]
[QTr  : EqNatTrans L N Q] 
[QEL  : EqNatLeftEuc L N Q]
[QtS  : EqNatToEqSucc L N Q S]
[QAL  : EqNatAddNatLeft L N Q A]
[An0  : AddNatZeroEqNat L N Q A Z]
[AnS  : AddNatSuccEqSucc L N Q A S]
: AddNatAssoc L N Q A := 
{toFun := addNatAssocByAddNatX I NS NAn0 NA QTr QEL QtS QAL An0 AnS}

instance iAddNatAssocByPeano
[FaN : LForallNat L N] [ent : LEnt L]
[I   : NatInduction L N Z S]
[N0  : NatZero L N Z]
[NS  : NatSuccNat L N S]
[NQ  : NatEqNat L N Q]
[QSm : EqNatSymm L N Q]
[QTr : EqNatTrans L N Q] 
[QtS : EqNatToEqSucc L N Q S]
[An0 : AddNatZeroEqNat L N Q A Z]
[AnS : AddNatSuccEqSucc L N Q A S]
: AddNatAssoc L N Q A :=
{toFun := 
  addNatAssocByAddNatX iNatInductionRight3ByForallNat 
    NS iNatAddNatZeroByAddNatZero iNatAddNatByPeano 
    QTr iEqNatLeftEucBySymmTransT QtS iEqNatAddNatLeftByPeano An0 AnS}

-- a + (b + c) = (a + b) + c 

def addNatAssocRevByAddNatX 
(I    : NatInductionRight3 L N Z S)
(NS   : NatSuccNat L N S)
(NAn0 : NatAddNatZero L N A Z)
(NA   : NatAddNat L N A)
(QTr  : EqNatTrans L N Q)
(QEL  : EqNatLeftEuc L N Q)
(QtS  : EqNatToEqSucc L N Q S)
(QAL  : EqNatAddNatLeft L N Q A)
(An0  : AddNatZeroEqNat L N Q A Z)
(AnS  : AddNatSuccEqSucc L N Q A S)
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
    intro c Nc AmAnSc_eq_AAmnSc a b Na Nb
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
      exact AmAnSc_eq_AAmnSc a b Na Nb
    case AAabSc_eq_SAAabc =>
      exact addNatSuccEqSucc NAab Nc

instance iAddNatAssocRevByAddNatX
[I    : NatInductionRight3 L N Z S]
[NS   : NatSuccNat L N S]
[NAn0 : NatAddNatZero L N A Z]
[NA   : NatAddNat L N A]
[QTr  : EqNatTrans L N Q] 
[QEL  : EqNatLeftEuc L N Q]
[QtS  : EqNatToEqSucc L N Q S]
[QAL  : EqNatAddNatLeft L N Q A]
[An0  : AddNatZeroEqNat L N Q A Z]
[AnS  : AddNatSuccEqSucc L N Q A S]
: AddNatAssocRev L N Q A := 
{toFun := addNatAssocRevByAddNatX I NS NAn0 NA QTr QEL QtS QAL An0 AnS}

instance iAddNatAssocRevByPeano 
[FaN : LForallNat L N] [ent : LEnt L]
[I   : NatInduction L N Z S]
[N0  : NatZero L N Z]
[NS  : NatSuccNat L N S]
[NQ  : NatEqNat L N Q]
[QSm : EqNatSymm L N Q]
[QTr : EqNatTrans L N Q] 
[QtS : EqNatToEqSucc L N Q S]
[An0 : AddNatZeroEqNat L N Q A Z]
[AnS : AddNatSuccEqSucc L N Q A S]
: AddNatAssocRev L N Q A := 
{toFun := 
  addNatAssocRevByAddNatX iNatInductionRight3ByForallNat 
    NS iNatAddNatZeroByAddNatZero iNatAddNatByPeano 
    QTr iEqNatLeftEucBySymmTransT QtS iEqNatAddNatLeftByPeano An0 AnS}

--------------------------------------------------------------------------------
-- Special Cases
--------------------------------------------------------------------------------

-- a + 1 = S a

def addNatOneEqSuccByNatAdd
(N0  : NatZero L N Z)
(N1  : NatOne L N O)
(NS  : NatSuccNat L N S)
(NA  : NatAddNat L N A)
(QTr : EqNatTrans L N Q)
(QtS : EqNatToEqSucc L N Q S)
(Q1S : OneEqSuccZero L Q Z O S)
(QAL : EqNatAddNatLeft L N Q A)  
(An0 : AddNatZeroEqNat L N Q A Z)
(AnS : AddNatSuccEqSucc L N Q A S)
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

instance iAddNatOneEqSuccByNatAdd
[N0  : NatZero L N Z]
[N1  : NatOne L N O]
[NS  : NatSuccNat L N S]
[NA  : NatAddNat L N A]
[QTr : EqNatTrans L N Q]
[QtS : EqNatToEqSucc L N Q S]
[Q1S : OneEqSuccZero L Q Z O S]
[QAL : EqNatAddNatLeft L N Q A] 
[An0 : AddNatZeroEqNat L N Q A Z]
[AnS : AddNatSuccEqSucc L N Q A S] 
: AddNatOneEqSucc L N Q A O S
:= {toFun := addNatOneEqSuccByNatAdd N0 N1 NS NA QTr QtS Q1S QAL An0 AnS}

def addNatOneEqSuccByNatEq
(N0  : NatZero L N Z)
(NS  : NatSuccNat L N S)
(NQ  : NatEqNat L N Q)
(QTr : EqNatTrans L N Q)
(QtS : EqNatToEqSucc L N Q S)
(Q1S : OneEqSuccZero L Q Z O S)
(QAL : EqNatAddNatLeft L N Q A) 
(An0 : AddNatZeroEqNat L N Q A Z)
(AnS : AddNatSuccEqSucc L N Q A S)
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

instance iAddNatOneEqSuccByNatEq
[N0  : NatZero L N Z]
[NS  : NatSuccNat L N S]
[NQ  : NatEqNat L N Q]
[QTr : EqNatTrans L N Q]
[QtS : EqNatToEqSucc L N Q S]
[Q1S : OneEqSuccZero L Q Z O S] 
[QAL : EqNatAddNatLeft L N Q A] 
[An0 : AddNatZeroEqNat L N Q A Z]
[AnS : AddNatSuccEqSucc L N Q A S]
: AddNatOneEqSucc L N Q A O S
:= {toFun := addNatOneEqSuccByNatEq N0 NS NQ QTr QtS Q1S QAL An0 AnS}

-- 1 + a = S a

def addOneNatEqSuccByNatAdd
(N0  : NatZero L N Z)
(N1  : NatOne L N O)
(NS  : NatSuccNat L N S)
(NA  : NatAddNat L N A)
(QTr : EqNatTrans L N Q)
(QtS : EqNatToEqSucc L N Q S)
(Q1S : OneEqSuccZero L Q Z O S)
(QAR : EqNatAddNatRight L N Q A)  
(A0n : AddZeroNatEqNat L N Q A Z)
(ASn : AddSuccNatEqSucc L N Q A S)
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

instance iAddOneNatEqSuccByNatAdd
[N0  : NatZero L N Z]
[N1  : NatOne L N O]
[NS  : NatSuccNat L N S]
[NA  : NatAddNat L N A]
[QTr : EqNatTrans L N Q]
[QtS : EqNatToEqSucc L N Q S]
[Q1S : OneEqSuccZero L Q Z O S]
[QAR : EqNatAddNatRight L N Q A]
[A0n : AddZeroNatEqNat L N Q A Z]
[ASn : AddSuccNatEqSucc L N Q A S]
: AddOneNatEqSucc L N Q A O S := 
  {toFun := 
    addOneNatEqSuccByNatAdd N0 N1 NS NA QTr QtS Q1S QAR A0n ASn}
