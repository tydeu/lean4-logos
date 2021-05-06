import Logos.Peano.Eq
import Logos.Peano.Add
import Logos.Peano.Rules
import Logos.Peano.Forall
import Logos.Peano.Induction
import Logos.Peano.Mul.Rules

universes u v
variable {P : Sort u} {T : Sort v} 

open Logos.Notation
namespace Logos.Peano

variable 
  {L : Logic P}
  [N : PNat P T] [Z : Zero T] [O : One T] [S : Succ T]
  [A : SAdd T] [M : SMul T]
  [Q : SEq P T]

--------------------------------------------------------------------------------
-- Closure
--------------------------------------------------------------------------------

-- nat (0 * 0)

instance iNatMulZeroNyMulZero 
[N0 : NatZero L N Z] [NQ : NatEqNat L N Q] [M0 : MulZeroEqZero L Q M Z] 
: NatMulZero L N M Z 
:= {toFun := natEq nat0 mulZeroEqZero}

instance iNatMulZeroByMulNatZero 
[N0 : NatZero L N Z] [NQ : NatEqNat L N Q] [Mn0 : MulNatZeroEqZero L N Q M Z] 
: NatMulZero L N M Z 
:= {toFun := natEq nat0 (mulNatZeroEqZero nat0)}

instance iNatMulZeroByMulZeroNat 
[N0 : NatZero L N Z] [NQ : NatEqNat L N Q] [M0n : MulZeroNatEqZero L N Q M Z] 
: NatMulZero L N M Z 
:= {toFun := natEq nat0 (mulZeroNatEqZero nat0)}

-- nat (a * 0)

def natMulNatZeroByInduction
(I    : NatInduction L N Z S)
(N0   : NatZero L N Z)
(NS   : NatSuccNat L N S)
(NQ   : NatEqNat L N Q)
(NA0n : NatAddZeroNat L N A Z)
(NM0  : NatMulZero L N M Z)
(MSn  : MulSuccNatEqAddMul L N Q M A S)
: (a : T) -> (L |- nat a) -> (L |- nat (a * 0))
:= by
  refine natInduction ?f0 ?fS
  case f0 =>
    exact natMulZero
  case fS =>
    intro a Na NA0a
    apply natEq (natAddZeroNat NA0a)
    exact mulSuccNatEqAddMul Na nat0 

instance iNatMulNatZeroByInduction
[I    : NatInduction L N Z S]
[N0   : NatZero L N Z]
[NS   : NatSuccNat L N S]
[NQ   : NatEqNat L N Q]
[NA0n : NatAddZeroNat L N A Z]
[NM0  : NatMulZero L N M Z]
[MSn  : MulSuccNatEqAddMul L N Q M A S]
: NatMulNatZero L N M Z 
:= {toFun := natMulNatZeroByInduction I N0 NS NQ NA0n NM0 MSn}

instance iNatMulNatZeroByMulNatZero 
[N0 : NatZero L N Z] [NQ : NatEqNat L N Q] [Mn0 : MulNatZeroEqZero L N Q M Z]
: NatMulNatZero L N M Z 
:= {toFun := fun _ Na => natEq nat0 (mulNatZeroEqZero Na)}

instance iNatMulNatZeroByNatMul
[N0 : NatZero L N Z] [NM : NatMulNat L N M] : NatMulNatZero L N M Z 
:= {toFun := fun _ Na => natMulNat Na nat0}

-- nat (0 * a)

def natMulZeroNatByInduction
(I    : NatInduction L N Z S)
(N0   : NatZero L N Z)
(NS   : NatSuccNat L N S)
(NQ   : NatEqNat L N Q)
(NA0n : NatAddZeroNat L N A Z)
(NM0  : NatMulZero L N M Z)
(MnS  : MulNatSuccEqAddMul L N Q M A S)
: (a : T) -> (L |- nat a) -> (L |- nat (0 * a))
:= by
  refine natInduction ?f0 ?fS
  case f0 =>
    exact natMulZero
  case fS =>
    intro a Na NA0a
    apply natEq (natAddZeroNat NA0a)
    exact mulNatSuccEqAddMul nat0 Na 

instance iNatMulZeroNatByInduction
[I    : NatInduction L N Z S]
[N0   : NatZero L N Z]
[NS   : NatSuccNat L N S]
[NQ   : NatEqNat L N Q]
[NA0n : NatAddZeroNat L N A Z]
[NM0  : NatMulZero L N M Z]
[MnS  : MulNatSuccEqAddMul L N Q M A S]
: NatMulZeroNat L N M Z 
:= {toFun := natMulZeroNatByInduction I N0 NS NQ NA0n NM0 MnS}

instance iNatMulZeroNatByMulZeroNat
[N0 : NatZero L N Z] [NQ : NatEqNat L N Q] [M0n : MulZeroNatEqZero L N Q M Z]
: NatMulZeroNat L N M Z 
:= {toFun := fun _ Na => natEq nat0 (mulZeroNatEqZero Na)}

instance iNatMulZeroNatByNatMul
[N0 : NatZero L N Z] [NM : NatMulNat L N M] : NatMulZeroNat L N M Z 
:= {toFun := fun _ Na => natMul nat0 Na}

-- nat (a * b)

def natMulNatProof
(I    : NatInductionRight L N Z S)
(NQ   : NatEqNat L N Q)
(NA   : NatAddNat L N A)
(NMn0 : NatMulNatZero L N M Z)
(Mn0  : MulNatZeroEqZero L N Q M Z)
(MnS  : MulNatSuccEqAddMul L N Q M A S)
: (a b : T) -> (L |- nat a) -> (L |- nat b) -> (L |- nat (a * b))
:= by
  refine natInductionRight ?f0 ?fS
  case f0 =>
    intro a Na 
    exact natMulNatZero Na
  case fS =>
    intro b Nb NMnb a Na
    have NMab := NMnb a Na
    apply natEq (natAdd Na NMab)
    exact mulNatSuccEqAddMul Na Nb 

instance iNatMulNat 
[I   : NatInductionRight L N Z S] 
[NQ  : NatEqNat L N Q]
[NA  : NatAddNat L N A]
[NMn0 : NatMulNatZero L N M Z]
[Mn0 : MulNatZeroEqZero L N Q M Z]
[MnS : MulNatSuccEqAddMul L N Q M A S]
: NatMulNat L N M 
:= {toFun := natMulNatProof I NQ NA NMn0 Mn0 MnS}

instance iNatMulNatByPeano 
[FaN : LForallNat L N]
[I   : NatInduction L N Z S]
[N0  : NatZero L N Z]
[NS  : NatSuccNat L N S]
[NQ  : NatEqNat L N Q]
[An0 : AddNatZeroEqNat L N Q A Z]
[AnS : AddNatSuccEqSucc L N Q A S]
[Mn0 : MulNatZeroEqZero L N Q M Z]
[MnS : MulNatSuccEqAddMul L N Q M A S]
: NatMulNat L N M := 
{toFun := 
  natMulNatProof iNatInductionRightByForallNat 
    NQ iNatAddNatByPeano iNatMulNatZeroByMulNatZero Mn0 MnS}

--------------------------------------------------------------------------------
-- Basic Cases
--------------------------------------------------------------------------------

-- 0 * 0 = 0

instance iMulZeroEqZeroByMulNatZero
[N : PNat P T] [Q : SEq P T] [M : SMul T] [Z : Zero T] 
[N0 : NatZero L N Z] [Mn0 : MulNatZeroEqZero L N Q M Z]
: MulZeroEqZero L Q M Z
:= {toFun := mulNatZeroEqZero nat0}

instance iMulZeroEqZeroByMulZeroNat
[N : PNat P T] [Q : SEq P T] [M : SMul T] [Z : Zero T] 
[N0 : NatZero L N Z] [M0n : MulZeroNatEqZero L N Q M Z]
: MulZeroEqZero L Q M Z
:= {toFun := mulZeroNatEqZero nat0}

-- a * 0 = 0

def mulNatZeroEqZeroProof 
(I    : NatInduction L N Z S)
(N0   : NatZero L N Z)
(NS   : NatSuccNat L N S)
(NA0n : NatAddZeroNat L N A Z)
(NMn0 : NatMulNatZero L N M Z)
(QTr  : EqNatTrans L N Q)
(M0   : MulZeroEqZero L Q M Z)
(A0n  : AddZeroNatEqNat L N Q A Z)
(MSn  : MulSuccNatEqAddMul L N Q M A S)
: (a : T) -> (L |- nat a) -> (L |- a * 0 = 0) 
:= by
  refine natInduction ?f0 ?fS
  case f0 => exact mulZeroEqZero
  case fS =>
    intro a Na Ma0_eq_0
    have NSa := natS Na
    have NMa0 := natMulNatZero Na
    have NMSa0 := natMulNatZero NSa
    have NA0Ma0 := natAddZeroNat NMa0
    apply eqNatTrans' NA0Ma0 NMSa0 nat0
    exact mulSuccNatEqAddMul Na nat0
    apply eqNatTrans' NMa0 NA0Ma0 nat0
    exact addZeroNatEqNat NMa0
    exact Ma0_eq_0

instance iMulNatZeroEqZero 
[I    : NatInduction L N Z S]
[N0   : NatZero L N Z]
[NS   : NatSuccNat L N S]
[NA0n : NatAddZeroNat L N A Z]
[NMn0 : NatMulNatZero L N M Z]
[QTr  : EqNatTrans L N Q]
[M0   : MulZeroEqZero L Q M Z]
[A0n  : AddZeroNatEqNat L N Q A Z]
[MSn  : MulSuccNatEqAddMul L N Q M A S]
: MulNatZeroEqZero L N Q M Z
:= {toFun := mulNatZeroEqZeroProof I N0 NS NA0n NMn0 QTr M0 A0n MSn}

instance iMulNatZeroEqZeroByNatEq 
[I   : NatInduction L N Z S]
[N0  : NatZero L N Z]
[NS  : NatSuccNat L N S]
[NQ  : NatEqNat L N Q]
[QTr : EqNatTrans L N Q]
[QtS : EqNatToEqSucc L N Q S]  
[M0  : MulZeroEqZero L Q M Z]
[A0  : AddZeroEqZero L Q A Z]
[AnS : AddNatSuccEqSucc L N Q A S]
[MSn : MulSuccNatEqAddMul L N Q M A S]
: MulNatZeroEqZero L N Q M Z := 
{toFun := 
  mulNatZeroEqZeroProof I 
    N0 NS iNatAddZeroNatByInduction iNatMulNatZeroByInduction 
    QTr M0 iAddZeroNatEqNatByNatEq MSn}

-- 0 * a = 0

def mulZeroNatEqZeroProof 
(I    : NatInduction L N Z S)
(N0   : NatZero L N Z)
(NS   : NatSuccNat L N S)
(NA0n : NatAddZeroNat L N A Z)
(NM0n : NatMulZeroNat L N M Z)
(QTr  : EqNatTrans L N Q)
(M0   : MulZeroEqZero L Q M Z)
(A0n  : AddZeroNatEqNat L N Q A Z)
(MnS  : MulNatSuccEqAddMul L N Q M A S)
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

instance iMulZeroNatEqZero 
[I    : NatInduction L N Z S]
[N0   : NatZero L N Z]
[NS   : NatSuccNat L N S]
[NA0n : NatAddZeroNat L N A Z]
[NM0n : NatMulZeroNat L N M Z]
[QTr  : EqNatTrans L N Q]
[M0   : MulZeroEqZero L Q M Z]
[A0n  : AddZeroNatEqNat L N Q A Z]
[MnS  : MulNatSuccEqAddMul L N Q M A S]
: MulZeroNatEqZero L N Q M Z
:= {toFun := mulZeroNatEqZeroProof I N0 NS NA0n NM0n QTr M0 A0n MnS}

instance iMulZeroNatEqZeroByNatEq 
[I   : NatInduction L N Z S]
[N0  : NatZero L N Z]
[NS  : NatSuccNat L N S]
[NQ  : NatEqNat L N Q]
[QTr : EqNatTrans L N Q]
[QtS : EqNatToEqSucc L N Q S]  
[M0  : MulZeroEqZero L Q M Z]
[A0  : AddZeroEqZero L Q A Z]
[AnS : AddNatSuccEqSucc L N Q A S]
[MnS : MulNatSuccEqAddMul L N Q M A S]
: MulZeroNatEqZero L N Q M Z := 
{toFun := 
  mulZeroNatEqZeroProof I 
    N0 NS iNatAddZeroNatByInduction iNatMulZeroNatByInduction 
    QTr M0 iAddZeroNatEqNatByNatEq MnS}

instance iMulZeroNatEqZeroByPeano 
[FaN : LForallNat L N]
[I   : NatInduction L N Z S]
[N0  : NatZero L N Z]
[NS  : NatSuccNat L N S]
[NQ  : NatEqNat L N Q]
[QTr : EqNatTrans L N Q]
[QtS : EqNatToEqSucc L N Q S]
[An0 : AddNatZeroEqNat L N Q A Z]
[AnS : AddNatSuccEqSucc L N Q A S]
[Mn0 : MulNatZeroEqZero L N Q M Z]
[MnS : MulNatSuccEqAddMul L N Q M A S]
: MulZeroNatEqZero L N Q M Z := 
{toFun := 
  mulZeroNatEqZeroProof I N0 NS iNatAddZeroNatByNatAdd iNatMulZeroNatByNatMul
    QTr iMulZeroEqZeroByMulNatZero iAddZeroNatEqNatByPeano MnS}

-- S a + b = b + (a * b)

def mulSuccNatEqAddMulProof 
(I   : NatInductionRight L N Z S)
(N0  : NatZero L N Z)
(NS  : NatSuccNat L N S)
(NA  : NatAddNat L N A)  
(NM  : NatMulNat L N M)
(QTr : EqNatTrans L N Q)
(QEL : EqNatLeftEuc L N Q)
(QtS : EqNatToEqSucc L N Q S)
(QAL : EqNatAddNatLeft L N Q A)
(QAR : EqNatAddNatRight L N Q A)
(ACm : AddNatComm L N Q A)
(AAs : AddNatAssoc L N Q A)
(AAr : AddNatAssocRev L N Q A)
(A0n : AddZeroNatEqNat L N Q A Z)
(ASn : AddSuccNatEqSucc L N Q A S)
(Mn0 : MulNatZeroEqZero L N Q M Z)
(MnS : MulNatSuccEqAddMul L N Q M A S)
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
    intro b Nb MSnb_eq_AbMnb a Na 
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
      exact MSnb_eq_AbMnb a Na
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

instance iMulSuccNatEqAddMul 
[I   : NatInductionRight L N Z S]
[N0  : NatZero L N Z]
[NS  : NatSuccNat L N S]
[NA  : NatAddNat L N A]  
[NM  : NatMulNat L N M]
[QTr : EqNatTrans L N Q]
[QEL : EqNatLeftEuc L N Q]
[QtS : EqNatToEqSucc L N Q S]
[QAL : EqNatAddNatLeft L N Q A]
[QAR : EqNatAddNatRight L N Q A]
[ACm : AddNatComm L N Q A]
[AAs : AddNatAssoc L N Q A]
[AAr : AddNatAssocRev L N Q A]
[A0n : AddZeroNatEqNat L N Q A Z]
[ASn : AddSuccNatEqSucc L N Q A S]
[Mn0 : MulNatZeroEqZero L N Q M Z]
[MnS : MulNatSuccEqAddMul L N Q M A S]
: MulSuccNatEqAddMul L N Q M A S := 
{toFun := 
  mulSuccNatEqAddMulProof I N0 NS NA NM QTr QEL QtS QAL QAR 
    ACm AAs AAr A0n ASn Mn0 MnS}

instance iMulSuccNatEqAddMulByPeano 
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
[Mn0 : MulNatZeroEqZero L N Q M Z]
[MnS : MulNatSuccEqAddMul L N Q M A S]
: MulSuccNatEqAddMul L N Q M A S := 
{toFun := 
  mulSuccNatEqAddMulProof 
    iNatInductionRightByForallNat 
    N0 NS iNatAddNatByPeano iNatMulNatByPeano 
    QTr iEqNatLeftEucBySymmTransT QtS 
    iEqNatAddNatLeftByPeano iEqNatAddNatRightByPeano 
    iAddNatCommByPeano iAddNatAssocByPeano iAddNatAssocRevByPeano 
    iAddZeroNatEqNatByPeano iAddSuccNatEqSuccByPeano Mn0 MnS}

--------------------------------------------------------------------------------
-- Commutativity
--------------------------------------------------------------------------------

-- a * 0 = 0 * a

def mulNatZeroCommByNatMulZero
(QEL  : EqNatLeftEuc L N Q)
(N0   : NatZero L N Z)
(NMn0 : NatMulNatZero L N M Z)
(NM0n : NatMulZeroNat L N M Z)
(M0n  : MulZeroNatEqZero L N Q M Z)
(Mn0  : MulNatZeroEqZero L N Q M Z)
: (a : T) -> (L |- nat a) -> (L |- a * 0 = 0 * a) 
:= by
  intro a Na
  apply eqNatLeftEuc nat0 
  exact natMulNatZero Na; exact natMulZeroNat Na
  exact mulNatZeroEqZero Na; exact mulZeroNatEqZero Na

instance iMulNatZeroCommByNatMulZero 
[QEL  : EqNatLeftEuc L N Q]
[N0   : NatZero L N Z]
[NMn0 : NatMulNatZero L N M Z]
[NM0n : NatMulZeroNat L N M Z]
[M0n  : MulZeroNatEqZero L N Q M Z]
[Mn0  : MulNatZeroEqZero L N Q M Z]
: MulNatZeroComm L N Q M Z
:= {toFun := mulNatZeroCommByNatMulZero QEL N0 NMn0 NM0n M0n Mn0}

-- a * b = b * a

def mulNatCommProof 
(I   : NatInductionRight L N Z S)
(NA  : NatAddNat L N A)  
(NM  : NatMulNat L N M)
(NS  : NatSuccNat L N S)
(QTr : EqNatTrans L N Q)
(QEL : EqNatLeftEuc L N Q)
(QAL : EqNatAddNatLeft L N Q A)
(M0C : MulNatZeroComm L N Q M Z)
(MSn : MulSuccNatEqAddMul L N Q M A S)
(MnS : MulNatSuccEqAddMul L N Q M A S)
: (a b : T) -> (L |- nat a) -> (L |- nat b) -> (L |- a * b = b * a) 
:= by
  refine natInductionRight ?f0 ?fS
  case f0 =>
    intro a Na
    exact mulNatZeroComm Na
  case fS =>
    intro b Nb Mnb_eq_Mbn a Na
    have NSb := natS Nb
    have NMab := natMul Na Nb 
    have NAaMab := natAdd Na NMab
    have NMba := natMul Nb Na 
    have NAaMba := natAdd Na NMba
    have NSMba := natS NMba
    have NMSba := natMul NSb Na
    have NMaSb := natMul Na NSb
    apply eqNatLeftEuc NAaMba NMaSb NMSba
      ?MaSb_eq_AaMba ?MSba_eq_AaMba
    case MaSb_eq_AaMba =>
      apply eqNatTrans' NAaMab NMaSb NAaMba
      exact mulNatSuccEqAddMul Na Nb
      apply eqNatAddNatLeft' Na NMab NMba
      exact Mnb_eq_Mbn a Na
    case MSba_eq_AaMba =>
      exact mulSuccNatEqAddMul Nb Na

instance iMulNatComm 
[I   : NatInductionRight L N Z S]
[NA  : NatAddNat L N A]  
[NM  : NatMulNat L N M]
[NS  : NatSuccNat L N S]
[QTr : EqNatTrans L N Q]
[QEL : EqNatLeftEuc L N Q]
[QAL : EqNatAddNatLeft L N Q A]
[M0C : MulNatZeroComm L N Q M Z]
[MSn : MulSuccNatEqAddMul L N Q M A S]
[MnS : MulNatSuccEqAddMul L N Q M A S]
: MulNatComm L N Q M 
:= {toFun := mulNatCommProof I NA NM NS QTr QEL QAL M0C MSn MnS}

instance iMulNatCommByPeano 
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
[Mn0 : MulNatZeroEqZero L N Q M Z]
[MnS : MulNatSuccEqAddMul L N Q M A S]
: MulNatComm L N Q M := 
{toFun := 
  mulNatCommProof iNatInductionRightByForallNat 
    iNatAddNatByPeano iNatMulNatByPeano NS 
    QTr iEqNatLeftEucBySymmTransT iEqNatAddNatLeftByPeano 
    iMulNatZeroCommByNatMulZero iMulSuccNatEqAddMulByPeano MnS}

--------------------------------------------------------------------------------
-- Substitutivity
--------------------------------------------------------------------------------

-- Left Multiplication
-- (a = b) -> (c * a = c * b)

def eqNatMulNatLeftProof
(I   : NatInductionRight3If L N Z S)
(N0  : NatZero L N Z)
(NS  : NatSuccNat L N S)
(NA  : NatAddNat L N A)
(NM  : NatMulNat L N M)
(QTr : EqNatTrans L N Q)
(QEL : EqNatLeftEuc L N Q)
(QAL : EqNatAddNatLeft L N Q A)
(QAR : EqNatAddNatRight L N Q A)
(M0n : MulZeroNatEqZero L N Q M Z)
(MSn : MulSuccNatEqAddMul L N Q M A S)
: (a b c : T) -> (L |- nat a) -> (L |- nat b) -> (L |- nat c) -> 
  ((L |- a = b) -> (L |- c * a = c * b)) 
:= by
  refine natInductionRight3If ?f0 ?fS
  case f0 =>
    intro a b Na Nb Qab
    apply eqNatLeftEuc nat0 (natMulZeroNat Na) (natMulZeroNat Nb) 
    exact mulZeroNatEqZero Na
    exact mulZeroNatEqZero Nb
  case fS =>
    intro c Nc Qmn_to_QMcmMcn a b Na Nb Qab 
    have NSc := natS Nc
    have NMcb := natMul Nc Nb
    have NMSca := natMul NSc Na
    have NMScb := natMul NSc Nb
    have NAbMcb := natAdd Nb NMcb
    apply eqNatLeftEuc NAbMcb NMSca NMScb
      ?MSca_eq_AbMcb ?MScb_eq_AbMcb
    case MSca_eq_AbMcb =>
      have NMca := natMul Nc Na
      have NAaMca := natAdd Na NMca
      have NAaMcb := natAdd Na NMcb
      apply eqNatTrans' NAaMca NMSca NAbMcb
      exact mulSuccNatEqAddMul Nc Na
      apply eqNatTrans' NAaMcb NAaMca NAbMcb
      apply eqNatAddNatLeft' Na NMca NMcb
      exact Qmn_to_QMcmMcn a b Na Nb Qab
      apply eqNatAddNatRight' NMcb Na Nb 
      exact Qab
    case MScb_eq_AbMcb =>
      exact mulSuccNatEqAddMul Nc Nb

instance iEqNatMulNatLeft
[I   : NatInductionRight3If L N Z S]
[N0  : NatZero L N Z]
[NS  : NatSuccNat L N S]
[NA  : NatAddNat L N A]
[NM  : NatMulNat L N M]
[QTr : EqNatTrans L N Q]
[QEL : EqNatLeftEuc L N Q]
[QAL : EqNatAddNatLeft L N Q A]
[QAR : EqNatAddNatRight L N Q A]
[M0n : MulZeroNatEqZero L N Q M Z]
[MSn : MulSuccNatEqAddMul L N Q M A S]
: EqNatMulNatLeft L N Q M := 
{toFun := 
  eqNatMulNatLeftProof I N0 NS NA NM QTr QEL QAL QAR M0n MSn}

instance iEqNatMulNatLeftByPeano
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
[Mn0 : MulNatZeroEqZero L N Q M Z]
[MnS : MulNatSuccEqAddMul L N Q M A S]
: EqNatMulNatLeft L N Q M := 
{toFun := 
  eqNatMulNatLeftProof iNatInductionRight3IfByForallNatIf 
    N0 NS iNatAddNatByPeano iNatMulNatByPeano 
    QTr iEqNatLeftEucBySymmTransT 
    iEqNatAddNatLeftByPeano iEqNatAddNatRightByPeano 
    iMulZeroNatEqZeroByPeano iMulSuccNatEqAddMulByPeano}

-- Right Multiplication
-- (a = b) -> (a * c = b * c)

def eqNatMulNatRightProof
(I   : NatInductionRight3If L N Z S)
(N0  : NatZero L N Z)
(NS  : NatSuccNat L N S)
(NA  : NatAddNat L N A)
(NM  : NatMulNat L N M)
(QTr : EqNatTrans L N Q)
(QEL : EqNatLeftEuc L N Q)
(QAL : EqNatAddNatLeft L N Q A)
(QAR : EqNatAddNatRight L N Q A)
(Mn0 : MulNatZeroEqZero L N Q M Z)
(MnS : MulNatSuccEqAddMul L N Q M A S)
: (a b c : T) -> (L |- nat a) -> (L |- nat b) -> (L |- nat c) -> 
  ((L |- a = b) -> (L |- a * c = b * c)) 
:= by
  refine natInductionRight3If ?f0 ?fS
  case f0 =>
    intro a b Na Nb Qab
    apply eqNatLeftEuc nat0 (natMulNatZero Na) (natMulNatZero Nb) 
    exact mulNatZeroEqZero Na
    exact mulNatZeroEqZero Nb
  case fS =>
    intro c Nc Qmn_to_QMmcMnc a b Na Nb Qab
    have NSc := natS Nc
    have NMbc := natMul Nb Nc
    have NMaSc := natMul Na NSc
    have NMbSc := natMul Nb NSc
    have NAbMbc := natAdd Nb NMbc
    apply eqNatLeftEuc NAbMbc NMaSc NMbSc
      ?MaSc_eq_AbMcb ?MbSc_eq_AbMbc
    case MaSc_eq_AbMcb =>
      have NMac := natMul Na Nc
      have NAaMac := natAdd Na NMac
      have NAaMbc := natAdd Na NMbc
      apply eqNatTrans' NAaMac NMaSc NAbMbc
      exact mulNatSuccEqAddMul Na Nc
      apply eqNatTrans' NAaMbc NAaMac NAbMbc
      apply eqNatAddNatLeft' Na NMac NMbc
      exact Qmn_to_QMmcMnc a b Na Nb Qab
      apply eqNatAddNatRight' NMbc Na Nb
      exact Qab
    case MbSc_eq_AbMbc =>
      exact mulNatSuccEqAddMul Nb Nc

instance iEqNatMulNatRight
[I   : NatInductionRight3If L N Z S]
[N0  : NatZero L N Z]
[NS  : NatSuccNat L N S]
[NA  : NatAddNat L N A]
[NM  : NatMulNat L N M]
[QTr : EqNatTrans L N Q]
[QEL : EqNatLeftEuc L N Q]
[QAL : EqNatAddNatLeft L N Q A]
[QAR : EqNatAddNatRight L N Q A]
[Mn0 : MulNatZeroEqZero L N Q M Z]
[MnS : MulNatSuccEqAddMul L N Q M A S]
: EqNatMulNatRight L N Q M := 
{toFun := 
  eqNatMulNatRightProof I N0 NS NA NM QTr QEL QAL QAR Mn0 MnS}

instance iEqNatMulNatRightByPeano
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
[Mn0 : MulNatZeroEqZero L N Q M Z]
[MnS : MulNatSuccEqAddMul L N Q M A S]
: EqNatMulNatRight L N Q M := 
{toFun := 
  eqNatMulNatRightProof iNatInductionRight3IfByForallNatIf 
    N0 NS iNatAddNatByPeano iNatMulNatByPeano QTr iEqNatLeftEucBySymmTransT 
    iEqNatAddNatLeftByPeano iEqNatAddNatRightByPeano Mn0 MnS}

--------------------------------------------------------------------------------
-- Distributivity
--------------------------------------------------------------------------------

-- Left Distributive Over Addition
-- a * (b + c) = (a * b) + (a * c)

def mulNatAddEqAddMulProof 
(I   : NatInductionRight3 L N Z S)
(N0  : NatZero L N Z)
(NS  : NatSuccNat L N S)
(NA  : NatAddNat L N A)
(NM  : NatMulNat L N M)
(QTr : EqNatTrans L N Q)
(QEL : EqNatLeftEuc L N Q)
(QAL : EqNatAddNatLeft L N Q A)
(QML : EqNatMulNatLeft L N Q M)
(ACm : AddNatComm L N Q A)
(AAs : AddNatAssoc L N Q A)
(An0 : AddNatZeroEqNat L N Q A Z)
(AnS : AddNatSuccEqSucc L N Q A S)
(Mn0 : MulNatZeroEqZero L N Q M Z)
(MnS : MulNatSuccEqAddMul L N Q M A S)
: (a b c : T) -> (L |- nat a) -> (L |- nat b) -> (L |- nat c) -> 
  (L |- a * (b + c) = (a * b) + (a * c)) 
:= by
  refine natInductionRight3 ?f0 ?fS
  case f0 =>
    intro a b Na Nb
    have NMab := natMul Na Nb
    have NAb0 := natAddNatZero Nb
    have NMaAb0 := natMul Na NAb0
    have NMa0 := natMulNatZero Na
    have NAMabMa0 := natAdd NMab NMa0
    apply eqNatLeftEuc NMab NMaAb0 NAMabMa0 
      ?MaAb0_eq_Mab ?AMabMa0_eq_Mab
    case MaAb0_eq_Mab =>
      apply eqNatMulNatLeft' Na NAb0 Nb
      exact addNatZeroEqNat Nb
    case AMabMa0_eq_Mab =>
      have NAMab0 := natAddNatZero NMab
      apply eqNatTrans' NAMab0 NAMabMa0 NMab
      apply eqNatAddNatLeft' NMab NMa0 nat0
      exact mulNatZeroEqZero Na
      exact addNatZeroEqNat NMab
  case fS =>
    intro c Nc MmAnc_eq_NAMmnMmc a b Na Nb
    have NSc := natS Nc
    have NMab := natMul Na Nb
    have NMac := natMul Na Nc 
    have NAMaca := natAdd NMac Na
    have NAMabAMaca := natAdd NMab NAMaca
    have NAbSc := natAdd Nb NSc
    have NMaAbSc := natMul Na NAbSc
    have NMaSc := natMul Na NSc
    have NAMabAaSc := natAdd NMab NMaSc
    apply eqNatLeftEuc NAMabAMaca NMaAbSc NAMabAaSc
      ?MaAbSc_eq_AMabAMaca ?AMabAaSc_eq_AMabAMaca
    case MaAbSc_eq_AMabAMaca =>
      have NAbc := natAdd Nb Nc
      have NSAbc := natS NAbc
      have NMaSAbc := natMul Na NSAbc
      have NMaAbc := natMul Na NAbc
      have NAaMaAbc := natAdd Na NMaAbc
      have NAMabMac := natAdd NMab NMac
      have NAaAMabMac := natAdd Na NAMabMac
      have NAAMabMaca := natAdd NAMabMac Na
      apply eqNatTrans' NMaSAbc NMaAbSc NAMabAMaca
      apply eqNatMulNatLeft' Na NAbSc NSAbc
      exact addNatSuccEqSucc Nb Nc
      apply eqNatTrans' NAaMaAbc NMaSAbc NAMabAMaca
      exact mulNatSuccEqAddMul Na NAbc
      apply eqNatTrans' NAaAMabMac NAaMaAbc NAMabAMaca
      apply eqNatAddNatLeft' Na NMaAbc NAMabMac
      exact MmAnc_eq_NAMmnMmc a b Na Nb
      apply eqNatTrans' NAAMabMaca NAaAMabMac NAMabAMaca
      exact addNatComm Na NAMabMac
      exact addNatAssoc NMab NMac Na
    case AMabAaSc_eq_AMabAMaca =>
      have NAaMac := natAdd Na NMac
      apply eqNatAddNatLeft' NMab NMaSc NAMaca
      apply eqNatTrans' NAaMac NMaSc NAMaca
      exact mulNatSuccEqAddMul Na Nc
      exact addNatComm Na NMac

instance iMulNatAddEqAddMul
[I   : NatInductionRight3 L N Z S]
[N0  : NatZero L N Z]
[NS  : NatSuccNat L N S]
[NA  : NatAddNat L N A]
[NM  : NatMulNat L N M]
[QTr : EqNatTrans L N Q]
[QEL : EqNatLeftEuc L N Q]
[QAL : EqNatAddNatLeft L N Q A]
[QML : EqNatMulNatLeft L N Q M]
[ACm : AddNatComm L N Q A]
[AAs : AddNatAssoc L N Q A]
[An0 : AddNatZeroEqNat L N Q A Z]
[AnS : AddNatSuccEqSucc L N Q A S]
[Mn0 : MulNatZeroEqZero L N Q M Z]
[MnS : MulNatSuccEqAddMul L N Q M A S]
: MulNatAddEqAddMul L N Q M A := 
{toFun := 
  mulNatAddEqAddMulProof I N0 NS NA NM QTr QEL QAL QML ACm AAs An0 AnS Mn0 MnS}

instance iMulNatAddEqAddMulByPeano
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
[Mn0 : MulNatZeroEqZero L N Q M Z]
[MnS : MulNatSuccEqAddMul L N Q M A S]
: MulNatAddEqAddMul L N Q M A := 
{toFun := 
  mulNatAddEqAddMulProof iNatInductionRight3ByForallNat 
    N0 NS iNatAddNatByPeano iNatMulNatByPeano QTr iEqNatLeftEucBySymmTransT 
    iEqNatAddNatLeftByPeano iEqNatMulNatLeftByPeano 
    iAddNatCommByPeano iAddNatAssocByPeano An0 AnS Mn0 MnS}

-- Right Distributive Over Addition
-- (b + c) * a = (b * a) + (c * a)

def mulAddNatEqAddMulProof 
(I   : NatInductionRight3 L N Z S)
(N0  : NatZero L N Z)
(NS  : NatSuccNat L N S)
(NA  : NatAddNat L N A)
(NM  : NatMulNat L N M)
(QTr : EqNatTrans L N Q)
(QEL : EqNatLeftEuc L N Q)
(QAL : EqNatAddNatLeft L N Q A)
(QMR : EqNatMulNatRight L N Q M)
(ACm : AddNatComm L N Q A)
(AAs : AddNatAssoc L N Q A)
(An0 : AddNatZeroEqNat L N Q A Z)
(AnS : AddNatSuccEqSucc L N Q A S)
(M0n : MulZeroNatEqZero L N Q M Z)
(MSn : MulSuccNatEqAddMul L N Q M A S)
: (a b c : T) -> (L |- nat a) -> (L |- nat b) -> (L |- nat c) -> 
  (L |- (b + c) * a = (b * a) + (c * a)) 
:= by
  refine natInductionRight3 ?f0 ?fS
  case f0 =>
    intro a b Na Nb
    have NMba := natMul Nb Na
    have NAb0 := natAddNatZero Nb
    have NMAb0a := natMul NAb0 Na
    have NM0a := natMulZeroNat Na
    have NAMbaM0a := natAdd NMba NM0a
    apply eqNatLeftEuc NMba NMAb0a NAMbaM0a 
      ?MAb0a_eq_Mba ?AMbaM0a_eq_Mba
    case MAb0a_eq_Mba =>
      apply eqNatMulNatRight' Na NAb0 Nb
      exact addNatZeroEqNat Nb
    case AMbaM0a_eq_Mba =>
      have NAMba0 := natAddNatZero NMba
      apply eqNatTrans' NAMba0 NAMbaM0a NMba
      apply eqNatAddNatLeft' NMba NM0a nat0
      exact mulZeroNatEqZero Na
      exact addNatZeroEqNat NMba
  case fS =>
    intro c Nc MAncm_eq_AMnmMcm a b Na Nb
    have NSc := natS Nc
    have NMba := natMul Nb Na
    have NMca := natMul Nc Na 
    have NAMcaa := natAdd NMca Na
    have NAMbaAMcaa := natAdd NMba NAMcaa
    have NAbSc := natAdd Nb NSc
    have NMAbSca := natMul NAbSc Na
    have NMSca := natMul NSc Na
    have NAMbaASca := natAdd NMba NMSca
    apply eqNatLeftEuc NAMbaAMcaa NMAbSca NAMbaASca
      ?AbSca_eq_AMbaASca ?AMbaAMcaa_eq_AMbaASca
    case AbSca_eq_AMbaASca =>
      have NAbc := natAdd Nb Nc
      have NSAbc := natS NAbc
      have NMSAbca := natMul NSAbc Na
      have NMAbca := natMul NAbc Na
      have NAaMaAbc := natAdd Na NMAbca
      have NAMbaMca := natAdd NMba NMca
      have NAaAMbaMca := natAdd Na NAMbaMca
      have NAAMabMaca := natAdd NAMbaMca Na
      apply eqNatTrans' NMSAbca NMAbSca NAMbaAMcaa
      apply eqNatMulNatRight' Na NAbSc NSAbc
      exact addNatSuccEqSucc Nb Nc
      apply eqNatTrans' NAaMaAbc NMSAbca NAMbaAMcaa
      exact mulSuccNatEqAddMul NAbc Na
      apply eqNatTrans' NAaAMbaMca NAaMaAbc NAMbaAMcaa
      apply eqNatAddNatLeft' Na NMAbca NAMbaMca
      exact MAncm_eq_AMnmMcm a b Na Nb
      apply eqNatTrans' NAAMabMaca NAaAMbaMca NAMbaAMcaa
      exact addNatComm Na NAMbaMca
      exact addNatAssoc NMba NMca Na
    case AMbaAMcaa_eq_AMbaASca =>
      have NAaMca := natAdd Na NMca
      apply eqNatAddNatLeft' NMba NMSca NAMcaa
      apply eqNatTrans' NAaMca NMSca NAMcaa
      exact mulSuccNatEqAddMul Nc Na 
      exact addNatComm Na NMca

instance iMulAddNatEqAddMul
[I   : NatInductionRight3 L N Z S]
[N0  : NatZero L N Z]
[NS  : NatSuccNat L N S]
[NA  : NatAddNat L N A]
[NM  : NatMulNat L N M]
[QTr : EqNatTrans L N Q]
[QEL : EqNatLeftEuc L N Q]
[QAL : EqNatAddNatLeft L N Q A]
[QMR : EqNatMulNatRight L N Q M]
[ACm : AddNatComm L N Q A]
[AAs : AddNatAssoc L N Q A]
[An0 : AddNatZeroEqNat L N Q A Z]
[AnS : AddNatSuccEqSucc L N Q A S]
[M0n : MulZeroNatEqZero L N Q M Z]
[MSn : MulSuccNatEqAddMul L N Q M A S]
: MulAddNatEqAddMul L N Q M A := 
{toFun := 
  mulAddNatEqAddMulProof I N0 NS NA NM QTr QEL QAL QMR ACm AAs An0 AnS M0n MSn}

instance iMulAddNatEqAddMulByPeano
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
[Mn0 : MulNatZeroEqZero L N Q M Z]
[MnS : MulNatSuccEqAddMul L N Q M A S]
: MulAddNatEqAddMul L N Q M A := 
{toFun := 
  mulAddNatEqAddMulProof iNatInductionRight3ByForallNat 
    N0 NS iNatAddNatByPeano iNatMulNatByPeano 
    QTr iEqNatLeftEucBySymmTransT 
    iEqNatAddNatLeftByPeano iEqNatMulNatRightByPeano 
    iAddNatCommByPeano iAddNatAssocByPeano An0 AnS 
    iMulZeroNatEqZeroByPeano iMulSuccNatEqAddMulByPeano}

--------------------------------------------------------------------------------
-- Associativity
--------------------------------------------------------------------------------

-- (a * b) * c = a * (b * c)

def mulNatAssocProof 
(I   : NatInductionRight3 L N Z S)
(N0  : NatZero L N Z)
(NS  : NatSuccNat L N S)
(NA  : NatAddNat L N A)  
(NM  : NatMulNat L N M)
(QTr : EqNatTrans L N Q)
(QEL : EqNatLeftEuc L N Q)
(QAL : EqNatAddNatLeft L N Q A)
(QML : EqNatMulNatLeft L N Q M)
(Mn0 : MulNatZeroEqZero L N Q M Z)
(MnS : MulNatSuccEqAddMul L N Q M A S)
(MnA : MulNatAddEqAddMul L N Q M A)
: (a b c : T) -> (L |- nat a) -> (L |- nat b) -> (L |- nat c) -> 
  (L |- (a * b) * c = a * (b * c)) 
:= by
  refine natInductionRight3 ?f0 ?fS
  case f0 =>
    intro a b Na Nb
    have NMab := natMul Na Nb
    have NMMab0 := natMulNatZero NMab
    have NMb0 := natMulNatZero Nb
    have NMaMb0 := natMul Na NMb0
    refine eqNatLeftEuc nat0 NMMab0 NMaMb0 ?MMab0_eq_0 ?MaMb0_eq_0
    case MMab0_eq_0 =>
      exact mulNatZeroEqZero NMab
    case MaMb0_eq_0 =>
      have NMa0 := natMulNatZero Na
      apply eqNatTrans' NMa0 NMaMb0 nat0
      apply eqNatMulNatLeft' Na NMb0 nat0
      exact mulNatZeroEqZero Nb
      exact mulNatZeroEqZero Na
  case fS =>
    intro c Nc MMmnc_eq_MmMnc a b Na Nb
    have NSc := natS Nc
    have NMab := natMul Na Nb
    have NMbc := natMul Nb Nc
    have NMaMbc := natMul Na NMbc
    have NAMabMaMbc := natAdd NMab NMaMbc 
    have NMMabSc := natMul NMab NSc
    have NMbSc := natMul Nb NSc
    have NMaMbSc := natMul Na NMbSc
    refine eqNatLeftEuc NAMabMaMbc NMMabSc NMaMbSc 
      ?MMabSc_eq_AMabMaMbc ?MaMbSc_eq_AMabMaMbc
    case MMabSc_eq_AMabMaMbc =>
      have NMMabc := natMul NMab Nc
      have NAMabMMabc := natAdd NMab NMMabc
      apply eqNatTrans' NAMabMMabc NMMabSc NAMabMaMbc
      exact mulNatSuccEqAddMul NMab Nc
      apply eqNatAddNatLeft' NMab NMMabc NMaMbc
      exact MMmnc_eq_MmMnc a b Na Nb
    case MaMbSc_eq_AMabMaMbc =>
      have NAbMbc := natAdd Nb NMbc
      have NMaAbMbc := natMul Na NAbMbc
      apply eqNatTrans' NMaAbMbc NMaMbSc NAMabMaMbc
      apply eqNatMulNatLeft' Na NMbSc NAbMbc
      exact mulNatSuccEqAddMul Nb Nc
      exact mulNatAddEqAddMul Na Nb NMbc

instance iMulNatAssoc 
[I   : NatInductionRight3 L N Z S]
[N0  : NatZero L N Z]
[NS  : NatSuccNat L N S]
[NA  : NatAddNat L N A]  
[NM  : NatMulNat L N M]
[QTr : EqNatTrans L N Q]
[QEL : EqNatLeftEuc L N Q]
[QAL : EqNatAddNatLeft L N Q A]
[QML : EqNatMulNatLeft L N Q M]
[Mn0 : MulNatZeroEqZero L N Q M Z]
[MnS : MulNatSuccEqAddMul L N Q M A S]
[MnA : MulNatAddEqAddMul L N Q M A]
: MulNatAssoc L N Q M 
:= {toFun := mulNatAssocProof I N0 NS NA NM QTr QEL QAL QML Mn0 MnS MnA}

instance iMulNatAssocByPeano 
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
[Mn0 : MulNatZeroEqZero L N Q M Z]
[MnS : MulNatSuccEqAddMul L N Q M A S]
: MulNatAssoc L N Q M := 
{toFun := 
  mulNatAssocProof iNatInductionRight3ByForallNat 
    N0 NS iNatAddNatByPeano iNatMulNatByPeano QTr iEqNatLeftEucBySymmTransT 
    iEqNatAddNatLeftByPeano iEqNatMulNatLeftByPeano Mn0 MnS 
    iMulNatAddEqAddMulByPeano}
