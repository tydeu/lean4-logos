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

instance iNatMulNatZeroByMulNatZero 
{P : Sort u} {T : Type v} {L : Logic P}
[N : IsNat P T] [Q : LEq P T] [M : Mul T] [Z : Zero T]  
[N0 : NatZero L N Z] [NQ : NatEqNat L N Q] [Mn0 : MulNatZeroEqZero L N Q M Z]
: NatMulNatZero L N M Z 
:= {natMulNatZero := fun _ Na => natEq nat0 (mulNatZeroEqZero Na)}

instance iNatMulNatZeroByNatMul
{P : Sort u} {T : Type v} {L : Logic P} 
[N : IsNat P T] [M : Mul T] [Z : Zero T] 
[N0 : NatZero L N Z] [NM : NatMulNat L N M] : NatMulNatZero L N M Z 
:= {natMulNatZero := fun _ Na => natMulNat Na nat0}

-- nat (0 * a)

instance iNatMulZeroNatByMulZeroNat
{P : Sort u} {T : Type v} {L : Logic P}
[N : IsNat P T] [Q : LEq P T] [M : Mul T] [Z : Zero T]  
[N0 : NatZero L N Z] [NQ : NatEqNat L N Q] [M0n : MulZeroNatEqZero L N Q M Z]
: NatMulZeroNat L N M Z 
:= {natMulZeroNat := fun _ Na => natEq nat0 (mulZeroNatEqZero Na)}

instance iNatMulZeroNatByNatMul
{P : Sort u} {T : Type v} {L : Logic P} 
[N : IsNat P T] [M : Mul T] [Z : Zero T] 
[N0 : NatZero L N Z] [NM : NatMulNat L N M] : NatMulZeroNat L N M Z 
:= {natMulZeroNat := fun _ Na => natMul nat0 Na}

-- nat (a * b)

def natMulNatProof
{P : Sort u} {T : Type v} {L : Logic P}
[N : PNat P T] [Q : LEq P T] [M : Mul T] [A : Add T]
(I    : NatInductionRight L N)
(NQ   : NatEqNat L N.toIsNat Q)
(NA   : NatAddNat L N.toIsNat A)
(NMn0 : NatMulNatZero L N.toIsNat M N.toZero)
(Mn0  : MulNatZeroEqZero L N.toIsNat Q M N.toZero)
(MnS  : MulNatSuccEqAddMul L N.toIsNat Q M A N.toSucc)
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

instance iNatMulNat 
{P : Sort u} {T : Type v} {L : Logic P} 
[N : PNat P T] [Q : LEq P T] [M : Mul T] [A : Add T]
[I   : NatInductionRight L N] 
[NQ  : NatEqNat L N.toIsNat Q]
[NA  : NatAddNat L N.toIsNat A]
[NMn0 : NatMulNatZero L N.toIsNat M N.toZero]
[Mn0 : MulNatZeroEqZero L N.toIsNat Q M N.toZero]
[MnS : MulNatSuccEqAddMul L N.toIsNat Q M A N.toSucc]
: NatMulNat L N.toIsNat M 
:= {natMulNat := natMulNatProof I NQ NA NMn0 Mn0 MnS}

instance iNatMulNatByPeano 
{P : Sort u} {T : Type v} {L : Logic P} 
[N : PNat P T] [Q : LEq P T] [M : Mul T] [A : Add T] 
[FaN : MForallNat L N.toIsNat]
[I   : NatInduction L N]
[N0  : NatZero L N.toIsNat N.toZero]
[NS  : NatSuccNat L N.toIsNat N.toSucc]
[NQ  : NatEqNat L N.toIsNat Q]
[An0 : AddNatZeroEqNat L N.toIsNat Q A N.toZero]
[AnS : AddNatSuccEqSucc L N.toIsNat Q A N.toSucc]
[Mn0 : MulNatZeroEqZero L N.toIsNat Q M N.toZero]
[MnS : MulNatSuccEqAddMul L N.toIsNat Q M A N.toSucc]
: NatMulNat L N.toIsNat M := 
{natMulNat := 
  natMulNatProof iNatInductionRightByForallNat 
    NQ iNatAddNatByPeano iNatMulNatZeroByMulNatZero Mn0 MnS}

--------------------------------------------------------------------------------
-- Special Cases
--------------------------------------------------------------------------------

-- 0 * 0 = 0

instance iMulZeroEqZeroByMulNatZero
{P : Sort u} {T : Type v} {L : Logic P}
[N : IsNat P T] [Q : LEq P T] [M : Mul T] [Z : Zero T] 
[N0 : NatZero L N Z] [Mn0 : MulNatZeroEqZero L N Q M Z]
: MulZeroEqZero L Q M Z
:= {mulZeroEqZero := mulNatZeroEqZero nat0}

instance iMulZeroEqZeroByMulZeroNat
{P : Sort u} {T : Type v} {L : Logic P}
[N : IsNat P T] [Q : LEq P T] [M : Mul T] [Z : Zero T] 
[N0 : NatZero L N Z] [M0n : MulZeroNatEqZero L N Q M Z]
: MulZeroEqZero L Q M Z
:= {mulZeroEqZero := mulZeroNatEqZero nat0}

--------------------------------------------------------------------------------
-- Commuted Axioms
--------------------------------------------------------------------------------

-- 0 * a = 0

def mulZeroNatEqZeroProof 
{P : Sort u} {T : Type v} {L : Logic P} 
{N : PNat P T} {Q : LEq P T} {M : Mul T} {A : Add T}
(I    : NatInduction L N)
(N0   : NatZero L N.toIsNat N.toZero)
(NS   : NatSuccNat L N.toIsNat N.toSucc)
(NA0n : NatAddZeroNat L N.toIsNat A N.toZero)
(NM0n : NatMulZeroNat L N.toIsNat M N.toZero)
(QTr  : EqNatTrans L N.toIsNat Q)
(M0   : MulZeroEqZero L Q M N.toZero)
(A0n  : AddZeroNatEqNat L N.toIsNat Q A N.toZero)
(MnS  : MulNatSuccEqAddMul L N.toIsNat Q M A N.toSucc)
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
{P : Sort u} {T : Type v} {L : Logic P} 
[N : PNat P T] [Q : LEq P T] [M : Mul T] [A : Add T]
[I    : NatInduction L N]
[N0   : NatZero L N.toIsNat N.toZero]
[NS   : NatSuccNat L N.toIsNat N.toSucc]
[NA0n : NatAddZeroNat L N.toIsNat A N.toZero]
[NM0n : NatMulZeroNat L N.toIsNat M N.toZero]
[QTr  : EqNatTrans L N.toIsNat Q]
[M0   : MulZeroEqZero L Q M N.toZero]
[A0n  : AddZeroNatEqNat L N.toIsNat Q A N.toZero]
[MnS  : MulNatSuccEqAddMul L N.toIsNat Q M A N.toSucc]
: MulZeroNatEqZero L N.toIsNat Q M N.toZero
:= {mulZeroNatEqZero := mulZeroNatEqZeroProof I N0 NS NA0n NM0n QTr M0 A0n MnS}

instance iMulZeroNatEqZeroByPeano 
{P : Sort u} {T : Type v} {L : Logic P} 
[N : PNat P T] [Q : LEq P T] [M : Mul T] [A : Add T] 
[FaN : MForallNat L N.toIsNat]
[I   : NatInduction L N]
[N0  : NatZero L N.toIsNat N.toZero]
[NS  : NatSuccNat L N.toIsNat N.toSucc]
[NQ  : NatEqNat L N.toIsNat Q]
[QTr : EqNatTrans L N.toIsNat Q]
[Q2S : EqNatToEqSucc L N.toIsNat Q N.toSucc]
[An0 : AddNatZeroEqNat L N.toIsNat Q A N.toZero]
[AnS : AddNatSuccEqSucc L N.toIsNat Q A N.toSucc]
[Mn0 : MulNatZeroEqZero L N.toIsNat Q M N.toZero]
[MnS : MulNatSuccEqAddMul L N.toIsNat Q M A N.toSucc]
: MulZeroNatEqZero L N.toIsNat Q M N.toZero := 
{mulZeroNatEqZero := 
  mulZeroNatEqZeroProof I N0 NS iNatAddZeroNatByNatAdd iNatMulZeroNatByMulZeroNat
    QTr iMulZeroEqZeroByMulNatZero iAddZeroNatEqNatByPeano MnS}

-- S a + b = b + (a * b)

def mulSuccNatEqAddMulProof 
{P : Sort u} {T : Type v} {L : Logic P} 
{N : PNat P T} {Q : LEq P T} {M : Mul T} {A : Add T} 
(I   : NatInductionRight L N)
(N0  : NatZero L N.toIsNat N.toZero)
(NS  : NatSuccNat L N.toIsNat N.toSucc)
(NA  : NatAddNat L N.toIsNat A)  
(NM  : NatMulNat L N.toIsNat M)
(QTr : EqNatTrans L N.toIsNat Q)
(QEL : EqNatLeftEuc L N.toIsNat Q)
(Q2S : EqNatToEqSucc L N.toIsNat Q N.toSucc)
(QAL : EqNatAddNatLeft L N.toIsNat Q A)
(QAR : EqNatAddNatRight L N.toIsNat Q A)
(ACm : AddNatComm L N.toIsNat Q A)
(AAs : AddNatAssoc L N.toIsNat Q A)
(AAr : AddNatAssocRev L N.toIsNat Q A)
(A0n : AddZeroNatEqNat L N.toIsNat Q A N.toZero)
(ASn : AddSuccNatEqSucc L N.toIsNat Q A N.toSucc)
(Mn0 : MulNatZeroEqZero L N.toIsNat Q M N.toZero)
(MnS : MulNatSuccEqAddMul L N.toIsNat Q M A N.toSucc)
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

instance iMulSuccNatEqAddMul 
{P : Sort u} {T : Type v} {L : Logic P} 
[N : PNat P T] [Q : LEq P T] [M : Mul T] [A : Add T]
[I   : NatInductionRight L N]
[N0  : NatZero L N.toIsNat N.toZero]
[NS  : NatSuccNat L N.toIsNat N.toSucc]
[NA  : NatAddNat L N.toIsNat A]  
[NM  : NatMulNat L N.toIsNat M]
[QTr : EqNatTrans L N.toIsNat Q]
[QEL : EqNatLeftEuc L N.toIsNat Q]
[Q2S : EqNatToEqSucc L N.toIsNat Q N.toSucc]
[QAL : EqNatAddNatLeft L N.toIsNat Q A]
[QAR : EqNatAddNatRight L N.toIsNat Q A]
[ACm : AddNatComm L N.toIsNat Q A]
[AAs : AddNatAssoc L N.toIsNat Q A]
[AAr : AddNatAssocRev L N.toIsNat Q A]
[A0n : AddZeroNatEqNat L N.toIsNat Q A N.toZero]
[ASn : AddSuccNatEqSucc L N.toIsNat Q A N.toSucc]
[Mn0 : MulNatZeroEqZero L N.toIsNat Q M N.toZero]
[MnS : MulNatSuccEqAddMul L N.toIsNat Q M A N.toSucc]
: MulSuccNatEqAddMul L N.toIsNat Q M A N.toSucc := 
{mulSuccNatEqAddMul := 
  mulSuccNatEqAddMulProof I N0 NS NA NM QTr QEL Q2S QAL QAR 
    ACm AAs AAr A0n ASn Mn0 MnS}

instance iMulSuccNatEqAddMulByPeano 
{P : Sort u} {T : Type v} {L : Logic P} 
[N : PNat P T] [Q : LEq P T] [M : Mul T] [A : Add T]
[FaN : MForallNat L N.toIsNat] [If : MIf L]
[I   : NatInduction L N]
[N0  : NatZero L N.toIsNat N.toZero]
[NS  : NatSuccNat L N.toIsNat N.toSucc]
[NQ  : NatEqNat L N.toIsNat Q]
[QSm : EqNatSymm L N.toIsNat Q]
[QTr : EqNatTrans L N.toIsNat Q]
[Q2S : EqNatToEqSucc L N.toIsNat Q N.toSucc]
[An0 : AddNatZeroEqNat L N.toIsNat Q A N.toZero]
[AnS : AddNatSuccEqSucc L N.toIsNat Q A N.toSucc]
[Mn0 : MulNatZeroEqZero L N.toIsNat Q M N.toZero]
[MnS : MulNatSuccEqAddMul L N.toIsNat Q M A N.toSucc]
: MulSuccNatEqAddMul L N.toIsNat Q M A N.toSucc := 
{mulSuccNatEqAddMul := 
  mulSuccNatEqAddMulProof 
    iNatInductionRightByForallNat 
    N0 NS iNatAddNatByPeano iNatMulNatByPeano 
    QTr iEqMemLeftEucToEqNatLeftEuc Q2S 
    iEqNatAddNatLeftByPeano iEqNatAddNatRightByPeano 
    iAddNatCommByPeano iAddNatAssocByPeano iAddNatAssocRevByPeano 
    iAddZeroNatEqNatByPeano iAddSuccNatEqSuccByPeano Mn0 MnS}

--------------------------------------------------------------------------------
-- Commutativity
--------------------------------------------------------------------------------

-- a * 0 = 0 * a

def mulNatZeroCommByNatMulZero
{P : Sort u} {T : Type v} {L : Logic P} 
{N : IsNat P T} {Q : LEq P T} {M : Mul T} {Z : Zero T}
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
{P : Sort u} {T : Type v} {L : Logic P} 
[N : IsNat P T] [Q : LEq P T] [M : Mul T] [Z : Zero T]
[QEL  : EqNatLeftEuc L N Q]
[N0   : NatZero L N Z]
[NMn0 : NatMulNatZero L N M Z]
[NM0n : NatMulZeroNat L N M Z]
[M0n  : MulZeroNatEqZero L N Q M Z]
[Mn0  : MulNatZeroEqZero L N Q M Z]
: MulNatZeroComm L N Q M Z
:= {mulNatZeroComm := mulNatZeroCommByNatMulZero QEL N0 NMn0 NM0n M0n Mn0}

-- a * b = b * a

def mulNatCommProof 
{P : Sort u} {T : Type v} {L : Logic P} 
{N : PNat P T} {Q : LEq P T} {M : Mul T} {A : Add T}
(I   : NatInductionRight L N)
(NA  : NatAddNat L N.toIsNat A)  
(NM  : NatMulNat L N.toIsNat M)
(NS  : NatSuccNat L N.toIsNat N.toSucc)
(QSm : EqNatSymm L N.toIsNat Q)
(QTr : EqNatTrans L N.toIsNat Q)
(QAL : EqNatAddNatLeft L N.toIsNat Q A)
(M0C : MulNatZeroComm L N.toIsNat Q M N.toZero)
(MSn : MulSuccNatEqAddMul L N.toIsNat Q M A N.toSucc)
(MnS : MulNatSuccEqAddMul L N.toIsNat Q M A N.toSucc)
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

instance iMulNatComm 
{P : Sort u} {T : Type v} {L : Logic P} 
[N : PNat P T] [Q : LEq P T] [M : Mul T] [A : Add T] 
[I   : NatInductionRight L N]
[NA  : NatAddNat L N.toIsNat A]  
[NM  : NatMulNat L N.toIsNat M]
[NS  : NatSuccNat L N.toIsNat N.toSucc]
[QSm : EqNatSymm L N.toIsNat Q]
[QTr : EqNatTrans L N.toIsNat Q]
[QAL : EqNatAddNatLeft L N.toIsNat Q A]
[M0C : MulNatZeroComm L N.toIsNat Q M N.toZero]
[MSn : MulSuccNatEqAddMul L N.toIsNat Q M A N.toSucc]
[MnS : MulNatSuccEqAddMul L N.toIsNat Q M A N.toSucc]
: MulNatComm L N.toIsNat Q M 
:= {mulNatComm := mulNatCommProof I NA NM NS QSm QTr QAL M0C MSn MnS}

instance iMulNatCommByPeano 
{P : Sort u} {T : Type v} {L : Logic P} 
[N : PNat P T] [Q : LEq P T] [M : Mul T] [A : Add T] 
[FaN : MForallNat L N.toIsNat] [If : MIf L]
[I   : NatInduction L N]
[N0  : NatZero L N.toIsNat N.toZero]
[NS  : NatSuccNat L N.toIsNat N.toSucc]
[NQ  : NatEqNat L N.toIsNat Q]
[QSm : EqNatSymm L N.toIsNat Q]
[QTr : EqNatTrans L N.toIsNat Q]
[Q2S : EqNatToEqSucc L N.toIsNat Q N.toSucc]
[An0 : AddNatZeroEqNat L N.toIsNat Q A N.toZero]
[AnS : AddNatSuccEqSucc L N.toIsNat Q A N.toSucc]
[Mn0 : MulNatZeroEqZero L N.toIsNat Q M N.toZero]
[MnS : MulNatSuccEqAddMul L N.toIsNat Q M A N.toSucc]
: MulNatComm L N.toIsNat Q M := 
{mulNatComm := mulNatCommProof iNatInductionRightByForallNat 
  iNatAddNatByPeano iNatMulNatByPeano NS QSm QTr iEqNatAddNatLeftByPeano 
  iMulNatZeroCommByNatMulZero iMulSuccNatEqAddMulByPeano MnS}

--------------------------------------------------------------------------------
-- Distributivity
--------------------------------------------------------------------------------

-- Left Distributive Over Addition
-- a * (b + c) = (a * b) + (a * c)

def mulNatAddEqAddMulProof 
{P : Sort u} {T : Type v} {L : Logic P} 
{N : PNat P T} {Q : LEq P T} {M : Mul T} {A : Add T}
(I   : NatInductionRight3 L N)
(N0  : NatZero L N.toIsNat N.toZero)
(NS  : NatSuccNat L N.toIsNat N.toSucc)
(NA  : NatAddNat L N.toIsNat A)
(NM  : NatMulNat L N.toIsNat M)
(QTr : EqNatTrans L N.toIsNat Q)
(QEL : EqNatLeftEuc L N.toIsNat Q)
(QAL : EqNatAddNatLeft L N.toIsNat Q A)
(QML : EqNatMulNatLeft L N.toIsNat Q M)
(ACm : AddNatComm L N.toIsNat Q A)
(AAs : AddNatAssoc L N.toIsNat Q A)
(An0 : AddNatZeroEqNat L N.toIsNat Q A N.toZero)
(AnS : AddNatSuccEqSucc L N.toIsNat Q A N.toSucc)
(Mn0 : MulNatZeroEqZero L N.toIsNat Q M N.toZero)
(MnS : MulNatSuccEqAddMul L N.toIsNat Q M A N.toSucc)
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
    intro a b c Na Nb Nc MaAbc_eq_NAMabMac
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
      exact MaAbc_eq_NAMabMac
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
{P : Sort u} {T : Type v} {L : Logic P} 
[N : PNat P T] [Q : LEq P T] [M : Mul T] [A : Add T]
[I   : NatInductionRight3 L N]
[N0  : NatZero L N.toIsNat N.toZero]
[NS  : NatSuccNat L N.toIsNat N.toSucc]
[NA  : NatAddNat L N.toIsNat A]
[NM  : NatMulNat L N.toIsNat M]
[QTr : EqNatTrans L N.toIsNat Q]
[QEL : EqNatLeftEuc L N.toIsNat Q]
[QAL : EqNatAddNatLeft L N.toIsNat Q A]
[QML : EqNatMulNatLeft L N.toIsNat Q M]
[ACm : AddNatComm L N.toIsNat Q A]
[AAs : AddNatAssoc L N.toIsNat Q A]
[An0 : AddNatZeroEqNat L N.toIsNat Q A N.toZero]
[AnS : AddNatSuccEqSucc L N.toIsNat Q A N.toSucc]
[Mn0 : MulNatZeroEqZero L N.toIsNat Q M N.toZero]
[MnS : MulNatSuccEqAddMul L N.toIsNat Q M A N.toSucc]
: MulNatAddEqAddMul L N.toIsNat Q M A := 
{mulNatAddEqAddMul := 
  mulNatAddEqAddMulProof I N0 NS NA NM QTr QEL QAL QML ACm AAs An0 AnS Mn0 MnS}

--------------------------------------------------------------------------------
-- Associativity
--------------------------------------------------------------------------------

def mulNatAssocProof 
{P : Sort u} {T : Type v} {L : Logic P} 
{N : PNat P T} {Q : LEq P T} {M : Mul T} {A : Add T}
(I   : NatInductionRight3 L N)
(N0  : NatZero L N.toIsNat N.toZero)
(NS  : NatSuccNat L N.toIsNat N.toSucc)
(NA  : NatAddNat L N.toIsNat A)  
(NM  : NatMulNat L N.toIsNat M)
(QTr : EqNatTrans L N.toIsNat Q)
(QEL : EqNatLeftEuc L N.toIsNat Q)
(QAL : EqNatAddNatLeft L N.toIsNat Q A)
(QML : EqNatMulNatLeft L N.toIsNat Q M)
(Mn0 : MulNatZeroEqZero L N.toIsNat Q M N.toZero)
(MnS : MulNatSuccEqAddMul L N.toIsNat Q M A N.toSucc)
(MnA : MulNatAddEqAddMul L N.toIsNat Q M A)
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
    intro a b c Na Nb Nc MMabc_eq_MaMbc
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
      exact MMabc_eq_MaMbc
    case MaMbSc_eq_AMabMaMbc =>
      have NAbMbc := natAdd Nb NMbc
      have NMaAbMbc := natMul Na NAbMbc
      apply eqNatTrans' NMaAbMbc NMaMbSc NAMabMaMbc
      apply eqNatMulNatLeft' Na NMbSc NAbMbc
      exact mulNatSuccEqAddMul Nb Nc
      exact mulNatAddEqAddMul Na Nb NMbc

instance iMulNatAssoc 
{P : Sort u} {T : Type v} {L : Logic P} 
[N : PNat P T] [Q : LEq P T] [M : Mul T] [A : Add T]
[I   : NatInductionRight3 L N]
[N0  : NatZero L N.toIsNat N.toZero]
[NS  : NatSuccNat L N.toIsNat N.toSucc]
[NA  : NatAddNat L N.toIsNat A]  
[NM  : NatMulNat L N.toIsNat M]
[QTr : EqNatTrans L N.toIsNat Q]
[QEL : EqNatLeftEuc L N.toIsNat Q]
[QAL : EqNatAddNatLeft L N.toIsNat Q A]
[QML : EqNatMulNatLeft L N.toIsNat Q M]
[Mn0 : MulNatZeroEqZero L N.toIsNat Q M N.toZero]
[MnS : MulNatSuccEqAddMul L N.toIsNat Q M A N.toSucc]
[MnA : MulNatAddEqAddMul L N.toIsNat Q M A]
: MulNatAssoc L N.toIsNat Q M 
:= {mulNatAssoc := mulNatAssocProof I N0 NS NA NM QTr QEL QAL QML Mn0 MnS MnA}

end Gaea.Peano