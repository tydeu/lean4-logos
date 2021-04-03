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

instance iNatAddZeroNyAddZero 
{P : Sort u} {T : Type v} {L : Logic P}
[N : IsNat P T] [Q : LEq P T] [A : Add T] [Z : Zero T]  
[N0 : NatZero L N Z] [NQ : NatEqNat L N Q] [A0 : AddZeroEqZero L Q A Z] 
: NatAddZero L N A Z 
:= {natAddZero := natEq nat0 addZeroEqZero}

instance iNatAddZeroByAddNatZero 
{P : Sort u} {T : Type v} {L : Logic P}
[N : IsNat P T] [Q : LEq P T] [A : Add T] [Z : Zero T]  
[N0 : NatZero L N Z] [NQ : NatEqNat L N Q] [An0 : AddNatZeroEqNat L N Q A Z] 
: NatAddZero L N A Z 
:= {natAddZero := natEq nat0 (addNatZeroEqNat nat0)}

instance iNatAddZeroByAddZeroNat 
{P : Sort u} {T : Type v} {L : Logic P}
[N : IsNat P T] [Q : LEq P T] [A : Add T] [Z : Zero T]  
[N0 : NatZero L N Z] [NQ : NatEqNat L N Q] [A0n : AddZeroNatEqNat L N Q A Z] 
: NatAddZero L N A Z 
:= {natAddZero := natEq nat0 (addZeroNatEqNat nat0)}

-- nat (a + 0)

def natAddNatZeroByInduction
{P : Sort u} {T : Type v} {L : Logic P} 
{N : PNat P T} {Q : LEq P T} {A : Add T}
(I   : NatInduction L N)
(N0  : NatZero L N.toIsNat N.toZero)
(NS  : NatSuccNat L N.toIsNat N.toSucc)
(NQ  : NatEqNat L N.toIsNat Q)
(NA0 : NatAddZero L N.toIsNat A N.toZero)
(ASn : AddSuccNatEqSucc L N.toIsNat Q A N.toSucc)
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
{P : Sort u} {T : Type v} {L : Logic P} 
[N : PNat P T] [Q : LEq P T] [A : Add T]
[I   : NatInduction L N]
[N0  : NatZero L N.toIsNat N.toZero]
[NS  : NatSuccNat L N.toIsNat N.toSucc]
[NQ  : NatEqNat L N.toIsNat Q] 
[NA0 : NatAddZero L N.toIsNat A N.toZero]
[ASn : AddSuccNatEqSucc L N.toIsNat Q A N.toSucc]
: NatAddNatZero L N.toIsNat A N.toZero 
:= {natAddNatZero := natAddNatZeroByInduction I N0 NS NQ NA0 ASn}

instance iNatAddNatZeroByAddNatZero 
{P : Sort u} {T : Type v} {L : Logic P}
[N : IsNat P T] [Q : LEq P T] [A : Add T] [Z : Zero T]  
[NQ : NatEqNat L N Q] [An0 : AddNatZeroEqNat L N Q A Z] : NatAddNatZero L N A Z 
:= {natAddNatZero := fun _ Na => natEq Na (addNatZeroEqNat Na)}

instance iNatAddNatZeroByNatAdd {P : Sort u} {T : Type v}
{L : Logic P} [N : IsNat P T] [A : Add T] [Z : Zero T] 
[N0 : NatZero L N Z] [NA : NatAddNat L N A] : NatAddNatZero L N A Z 
:= {natAddNatZero := fun _ Na => natAdd Na nat0}

-- nat (0 + a)

def natAddZeroNatByInduction
{P : Sort u} {T : Type v} {L : Logic P}
{N : PNat P T} {Q : LEq P T} {A : Add T}
(I   : NatInduction L N)
(N0  : NatZero L N.toIsNat N.toZero)
(NS  : NatSuccNat L N.toIsNat N.toSucc)
(NQ  : NatEqNat L N.toIsNat Q)
(NA0 : NatAddZero L N.toIsNat A N.toZero)
(AnS : AddNatSuccEqSucc L N.toIsNat Q A N.toSucc)
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
{P : Sort u} {T : Type v} {L : Logic P} 
[N : PNat P T] [Q : LEq P T] [A : Add T]
[I   : NatInduction L N]
[N0  : NatZero L N.toIsNat N.toZero]
[NS  : NatSuccNat L N.toIsNat N.toSucc]
[NQ  : NatEqNat L N.toIsNat Q] 
[NA0 : NatAddZero L N.toIsNat A N.toZero]
[An0 : AddNatSuccEqSucc L N.toIsNat Q A N.toSucc]
: NatAddZeroNat L N.toIsNat A N.toZero 
:= {natAddZeroNat :=  natAddZeroNatByInduction I N0 NS NQ NA0 An0}

instance iNatAddZeroNatByAddZeroNat 
{P : Sort u} {T : Type v} {L : Logic P}
[N : IsNat P T] [Q : LEq P T] [A : Add T] [Z : Zero T]  
[NQ : NatEqNat L N Q] [A0n : AddZeroNatEqNat L N Q A Z] : NatAddZeroNat L N A Z 
:= {natAddZeroNat := fun _ Na => natEq Na (addZeroNatEqNat Na)}

instance iNatAddZeroNatByNatAdd 
{P : Sort u} {T : Type v} {L : Logic P} 
[N : IsNat P T] [A : Add T] [Z : Zero T] 
[N0 : NatZero L N Z] [NA : NatAddNat L N A] : NatAddZeroNat L N A Z 
:= {natAddZeroNat := fun _ Na => natAdd nat0 Na}

-- nat (a + b)

def natAddNatByPeano 
{P : Sort u} {T : Type v} {L : Logic P}
{N : PNat P T} {Q : LEq P T} {A : Add T}
(I   : NatInductionRight L N)
(NQ  : NatEqNat L N.toIsNat Q)
(NS  : NatSuccNat L N.toIsNat N.toSucc)
(An0 : AddNatZeroEqNat L N.toIsNat Q A N.toZero)
(AnS : AddNatSuccEqSucc L N.toIsNat Q A N.toSucc)
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

instance iNatAddNatByPeano 
{P : Sort u} {T : Type v} {L : Logic P} 
[N : PNat P T] [Q : LEq P T] [A : Add T] [FaN : MForallNat L N.toIsNat]
[I   : NatInduction L N]
[NQ  : NatEqNat L N.toIsNat Q] 
[NS  : NatSuccNat L N.toIsNat N.toSucc]
[An0 : AddNatZeroEqNat L N.toIsNat Q A N.toZero] 
[AnS : AddNatSuccEqSucc L N.toIsNat Q A N.toSucc]
: NatAddNat L N.toIsNat A := 
  {natAddNat := natAddNatByPeano iNatInductionRightByForallNat NQ NS An0 AnS}

--------------------------------------------------------------------------------
-- Basic Cases
--------------------------------------------------------------------------------

-- 0 + 0 = 0

instance iAddZeroEqZeroByAddNatZero
{P : Sort u} {T : Type v} {L : Logic P}
[N : IsNat P T] [Q : LEq P T] [A : Add T] [Z : Zero T] 
[N0 : NatZero L N Z] [An0 : AddNatZeroEqNat L N Q A Z]
: AddZeroEqZero L Q A Z
:= {addZeroEqZero := addNatZeroEqNat nat0}

instance iAddZeroEqZeroByAddZeroNat
{P : Sort u} {T : Type v} {L : Logic P}
[N : IsNat P T] [Q : LEq P T] [A : Add T] [Z : Zero T] 
[N0 : NatZero L N Z] [A0n : AddZeroNatEqNat L N Q A Z]
: AddZeroEqZero L Q A Z
:= {addZeroEqZero := addZeroNatEqNat nat0}

-- a + 0 = 0

def addNatZeroEqNatByNatAdd
{P : Sort u} {T : Type v} {L : Logic P} 
{N : PNat P T} {Q : LEq P T} {A : Add T} 
(I    : NatInduction L N)
(N0   : NatZero L N.toIsNat N.toZero) 
(NS   : NatSuccNat L N.toIsNat N.toSucc)
(NAn0 : NatAddNatZero L N.toIsNat A N.toZero)
(QTr  : EqNatTrans L N.toIsNat Q) 
(QtS  : EqNatToEqSucc L N.toIsNat Q N.toSucc)  
(A0   : AddZeroEqZero L Q A N.toZero)
(ASn  : AddSuccNatEqSucc L N.toIsNat Q A N.toSucc)
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
{P : Sort u} {T : Type v} {L : Logic P} 
[N : PNat P T] [Q : LEq P T] [A : Add T] 
[I    : NatInduction L N]
[N0   : NatZero L N.toIsNat N.toZero] 
[NS   : NatSuccNat L N.toIsNat N.toSucc]
[NAn0 : NatAddNatZero L N.toIsNat A N.toZero]
[QTr  : EqNatTrans L N.toIsNat Q] 
[QtS  : EqNatToEqSucc L N.toIsNat Q N.toSucc]  
[A0   : AddZeroEqZero L Q A N.toZero]
[ASn  : AddSuccNatEqSucc L N.toIsNat Q A N.toSucc]
: AddNatZeroEqNat L N.toIsNat Q A N.toZero
:= {addNatZeroEqNat := addNatZeroEqNatByNatAdd I N0 NS NAn0 QTr QtS A0 ASn} 

instance iAddNatZeroEqNatByNatEq 
{P : Sort u} {T : Type v} {L : Logic P} 
[N : PNat P T] [Q : LEq P T] [A : Add T] 
[I   : NatInduction L N]
[N0  : NatZero L N.toIsNat N.toZero] 
[NS  : NatSuccNat L N.toIsNat N.toSucc]
[NQ  : NatEqNat L N.toIsNat Q]
[QTr : EqNatTrans L N.toIsNat Q] 
[QtS : EqNatToEqSucc L N.toIsNat Q N.toSucc]  
[A0  : AddZeroEqZero L Q A N.toZero]
[ASn : AddSuccNatEqSucc L N.toIsNat Q A N.toSucc]
: AddNatZeroEqNat L N.toIsNat Q A N.toZero :=
{addNatZeroEqNat := 
  addNatZeroEqNatByNatAdd I N0 NS iNatAddNatZeroByInduction QTr QtS A0 ASn} 

-- 0 + a = 0

def addZeroNatEqNatByNatAdd
{P : Sort u} {T : Type v} {L : Logic P} 
{N : PNat P T} {Q : LEq P T} {A : Add T} 
(I    : NatInduction L N)
(N0   : NatZero L N.toIsNat N.toZero) 
(NS   : NatSuccNat L N.toIsNat N.toSucc)
(NA0n : NatAddZeroNat L N.toIsNat A N.toZero)
(QTr  : EqNatTrans L N.toIsNat Q) 
(QtS  : EqNatToEqSucc L N.toIsNat Q N.toSucc)  
(A0   : AddZeroEqZero L Q A N.toZero)
(AnS  : AddNatSuccEqSucc L N.toIsNat Q A N.toSucc)
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
{P : Sort u} {T : Type v} {L : Logic P} 
[N : PNat P T] [Q : LEq P T] [A : Add T] 
[I    : NatInduction L N]
[N0   : NatZero L N.toIsNat N.toZero] 
[NS   : NatSuccNat L N.toIsNat N.toSucc]
[NA0n : NatAddZeroNat L N.toIsNat A N.toZero]
[QTr  : EqNatTrans L N.toIsNat Q] 
[QtS  : EqNatToEqSucc L N.toIsNat Q N.toSucc]  
[A0   : AddZeroEqZero L Q A N.toZero]
[AnS  : AddNatSuccEqSucc L N.toIsNat Q A N.toSucc]
: AddZeroNatEqNat L N.toIsNat Q A N.toZero
:= {addZeroNatEqNat := addZeroNatEqNatByNatAdd I N0 NS NA0n QTr QtS A0 AnS} 

instance iAddZeroNatEqNatByNatEq 
{P : Sort u} {T : Type v} {L : Logic P} 
[N : PNat P T] [Q : LEq P T] [A : Add T] 
[I   : NatInduction L N]
[N0  : NatZero L N.toIsNat N.toZero] 
[NS  : NatSuccNat L N.toIsNat N.toSucc]
[NQ  : NatEqNat L N.toIsNat Q]
[QTr : EqNatTrans L N.toIsNat Q] 
[QtS : EqNatToEqSucc L N.toIsNat Q N.toSucc]  
[A0  : AddZeroEqZero L Q A N.toZero]
[AnS : AddNatSuccEqSucc L N.toIsNat Q A N.toSucc]
: AddZeroNatEqNat L N.toIsNat Q A N.toZero := 
{addZeroNatEqNat := 
  addZeroNatEqNatByNatAdd I N0 NS iNatAddZeroNatByInduction QTr QtS A0 AnS} 

instance iAddZeroNatEqNatByPeano 
{P : Sort u} {T : Type v} {L : Logic P} 
[N : PNat P T] [Q : LEq P T] [A : Add T] [FaN : MForallNat L N.toIsNat]
[I   : NatInduction L N]
[N0  : NatZero L N.toIsNat N.toZero] 
[NS  : NatSuccNat L N.toIsNat N.toSucc]
[NQ  : NatEqNat L N.toIsNat Q]
[QTr : EqNatTrans L N.toIsNat Q] 
[QtS : EqNatToEqSucc L N.toIsNat Q N.toSucc]  
[An0 : AddNatZeroEqNat L N.toIsNat Q A N.toZero]
[AnS : AddNatSuccEqSucc L N.toIsNat Q A N.toSucc]
: AddZeroNatEqNat L N.toIsNat Q A N.toZero := 
{addZeroNatEqNat := 
  addZeroNatEqNatByNatAdd I N0 NS iNatAddZeroNatByNatAdd 
    QTr QtS iAddZeroEqZeroByAddNatZero AnS}

-- a + S b = S (a + b)

def addNatSuccEqSuccByNatAdd
{P : Sort u} {T : Type v} {L : Logic P} 
{N : PNat P T} {Q : LEq P T} {A : Add T}
(I    : NatInductionLeft L N)
(NS   : NatSuccNat L N.toIsNat N.toSucc)
(NA0n : NatAddZeroNat L N.toIsNat A N.toZero)
(NA   : NatAddNat L N.toIsNat A)
(QTr  : EqNatTrans L N.toIsNat Q)
(QEL  : EqNatLeftEuc L N.toIsNat Q)
(QtS  : EqNatToEqSucc L N.toIsNat Q N.toSucc)  
(A0n  : AddZeroNatEqNat L N.toIsNat Q A N.toZero)
(ASn  : AddSuccNatEqSucc L N.toIsNat Q A N.toSucc)
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
    intro a b Na Nb AaSb_eq_SAab
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
      exact AaSb_eq_SAab
    case SASab_eq_SSAab =>
      apply eqNatToEqSucc NASab NSAab 
      exact addSuccNatEqSucc Na Nb

instance iAddNatSuccEqSuccByNatAdd 
{P : Sort u} {T : Type v} {L : Logic P} 
[N : PNat P T] [Q : LEq P T] [A : Add T]
[I   : NatInductionLeft L N]
[NS  : NatSuccNat L N.toIsNat N.toSucc]
[NA0n : NatAddZeroNat L N.toIsNat A N.toZero]
[NA  : NatAddNat L N.toIsNat A]
[QTr : EqNatTrans L N.toIsNat Q]
[QEL : EqNatLeftEuc L N.toIsNat Q]
[QtS : EqNatToEqSucc L N.toIsNat Q N.toSucc]  
[A0n : AddZeroNatEqNat L N.toIsNat Q A N.toZero]
[ASn : AddSuccNatEqSucc L N.toIsNat Q A N.toSucc]
: AddNatSuccEqSucc L N.toIsNat Q A N.toSucc := 
{addNatSuccEqSucc := addNatSuccEqSuccByNatAdd I NS NA0n NA QTr QEL QtS A0n ASn}

-- S a + b = S (a + b)

def addSuccNatEqSuccByNatAdd
{P : Sort u} {T : Type v} {L : Logic P} 
{N : PNat P T} {Q : LEq P T} {A : Add T}
(I    : NatInductionRight L N)
(NS   : NatSuccNat L N.toIsNat N.toSucc)
(NAn0 : NatAddNatZero L N.toIsNat A N.toZero)
(NA   : NatAddNat L N.toIsNat A)
(QTr  : EqNatTrans L N.toIsNat Q)
(QEL  : EqNatLeftEuc L N.toIsNat Q)
(QtS  : EqNatToEqSucc L N.toIsNat Q N.toSucc)  
(An0  : AddNatZeroEqNat L N.toIsNat Q A N.toZero)
(AnS  : AddNatSuccEqSucc L N.toIsNat Q A N.toSucc)
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
    intro a b Na Nb ASab_eq_SAab
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
      exact ASab_eq_SAab
    case SAaSb_eq_SSAab =>
      apply eqNatToEqSucc NAaSb NSAab 
      exact addNatSuccEqSucc Na Nb

instance iAddSuccNatEqSuccByNatAdd 
{P : Sort u} {T : Type v} {L : Logic P} 
[N : PNat P T] [Q : LEq P T] [A : Add T]
[I   : NatInductionRight L N]
[NS  : NatSuccNat L N.toIsNat N.toSucc]
[NAn0 : NatAddNatZero L N.toIsNat A N.toZero]
[NA  : NatAddNat L N.toIsNat A]
[QTr : EqNatTrans L N.toIsNat Q]
[QEL : EqNatLeftEuc L N.toIsNat Q]
[QtS : EqNatToEqSucc L N.toIsNat Q N.toSucc]  
[An0 : AddNatZeroEqNat L N.toIsNat Q A N.toZero]
[AnS : AddNatSuccEqSucc L N.toIsNat Q A N.toSucc]
: AddSuccNatEqSucc L N.toIsNat Q A N.toSucc := 
{addSuccNatEqSucc := addSuccNatEqSuccByNatAdd I NS NAn0 NA QTr QEL QtS An0 AnS} 

instance iAddSuccNatEqSuccByPeano 
{P : Sort u} {T : Type v} {L : Logic P} 
[N : PNat P T] [Q : LEq P T] [A : Add T] [FaN : MForallNat L N.toIsNat]
[I   : NatInduction L N]
[N0  : NatZero L N.toIsNat N.toZero]
[NS  : NatSuccNat L N.toIsNat N.toSucc]
[NQ  : NatEqNat L N.toIsNat Q]
[QSm : EqNatSymm L N.toIsNat Q]
[QTr : EqNatTrans L N.toIsNat Q]
[QtS : EqNatToEqSucc L N.toIsNat Q N.toSucc]  
[An0 : AddNatZeroEqNat L N.toIsNat Q A N.toZero]
[AnS : AddNatSuccEqSucc L N.toIsNat Q A N.toSucc]
: AddSuccNatEqSucc L N.toIsNat Q A N.toSucc := 
{addSuccNatEqSucc := 
  addSuccNatEqSuccByNatAdd iNatInductionRightByForallNat 
    NS iNatAddNatZeroByNatAdd iNatAddNatByPeano 
    QTr iEqNatLeftEucOfLeftEucT QtS An0 AnS} 

--------------------------------------------------------------------------------
-- Commutativity
--------------------------------------------------------------------------------

-- 0 + a = a + 0

def addNatZeroCommByNatAddZero
{P : Sort u} {T : Type v} {L : Logic P} 
{N : IsNat P T} {Q : LEq P T} {A : Add T} {Z : Zero T}
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
{P : Sort u} {T : Type v} {L : Logic P} 
[N : IsNat P T] [Q : LEq P T] [A : Add T] [Z : Zero T]
[QEL  : EqNatLeftEuc L N Q] 
[NAn0 : NatAddNatZero L N A Z] 
[NA0n : NatAddZeroNat L N A Z]
[An0  : AddNatZeroEqNat L N Q A Z] 
[A0n  : AddZeroNatEqNat L N Q A Z]
: AddNatZeroComm L N Q A Z 
:= {addNatZeroComm := addNatZeroCommByNatAddZero QEL NAn0 NA0n An0 A0n}

instance iAddNatZeroCommByNatAdd
{P : Sort u} {T : Type v} {L : Logic P} 
[N : IsNat P T] [Q : LEq P T] [A : Add T] [Z : Zero T]
[QEL : EqNatLeftEuc L N Q]
[N0  : NatZero L N Z] 
[NA  : NatAddNat L N A] 
[An0 : AddNatZeroEqNat L N Q A Z] 
[A0n : AddZeroNatEqNat L N Q A Z]
: AddNatZeroComm L N Q A Z := 
{addNatZeroComm := addNatZeroCommByNatAddZero QEL 
  iNatAddNatZeroByNatAdd iNatAddZeroNatByNatAdd An0 A0n}

instance iAddNatZeroCommByNatEq
{P : Sort u} {T : Type v} {L : Logic P} 
[N : IsNat P T] [Q : LEq P T] [A : Add T] [Z : Zero T]
[NQ  : NatEqNat L N Q]
[QSm : EqNatSymm L N Q]
[QTr : EqNatTrans L N Q] 
[An0 : AddNatZeroEqNat L N Q A Z] 
[A0n : AddZeroNatEqNat L N Q A Z]
: AddNatZeroComm L N Q A Z := 
{addNatZeroComm := addNatZeroCommByNatAddZero iEqNatLeftEucOfLeftEucT 
  iNatAddNatZeroByAddNatZero iNatAddZeroNatByAddZeroNat An0 A0n}

def addNatZeroCommByLeftEucNat
{P : Sort u} {T : Type v} {L : Logic P} 
{N : IsNat P T} {Q : LEq P T} {A : Add T} {Z : Zero T}
(QEL : EqLeftEucNat L N Q)
(An0 : AddNatZeroEqNat L N Q A Z)
(A0n : AddZeroNatEqNat L N Q A Z)
: (a : T) -> (L |- nat a) -> (L |- a + 0 = 0 + a)
:= by
  intro a Na; apply eqLeftEucNat Na
  exact addNatZeroEqNat Na; exact addZeroNatEqNat Na 

instance iAddNatZeroCommByLeftEucNat
{P : Sort u} {T : Type v} {L : Logic P} 
[N : IsNat P T] [Q : LEq P T] [A : Add T] [Z : Zero T]
[QEL : EqLeftEucNat L N Q] 
[An0 : AddNatZeroEqNat L N Q A Z] 
[A0n : AddZeroNatEqNat L N Q A Z]
: AddNatZeroComm L N Q A Z 
:= {addNatZeroComm := addNatZeroCommByLeftEucNat QEL An0 A0n}

instance iAddNatZeroCommByPeano
{P : Sort u} {T : Type v} {L : Logic P} 
[N : PNat P T] [Q : LEq P T] [A : Add T] [FaN : MForallNat L N.toIsNat] 
[I   : NatInduction L N]
[N0  : NatZero L N.toIsNat N.toZero] 
[NS  : NatSuccNat L N.toIsNat N.toSucc]
[NQ  : NatEqNat L N.toIsNat Q]
[QSm : EqNatSymm L N.toIsNat Q]
[QTr : EqNatTrans L N.toIsNat Q] 
[QtS : EqNatToEqSucc L N.toIsNat Q N.toSucc]  
[An0 : AddNatZeroEqNat L N.toIsNat Q A N.toZero]
[AnS : AddNatSuccEqSucc L N.toIsNat Q A N.toSucc]
: AddNatZeroComm L N.toIsNat Q A N.toZero := 
{addNatZeroComm := addNatZeroCommByLeftEucNat iEqLeftEucNatByNatEq 
  An0 iAddZeroNatEqNatByPeano}

-- a + b = b + a

def addNatCommProof
{P : Sort u} {T : Type v} {L : Logic P} 
{N : PNat P T} {Q : LEq P T} {A : Add T}
(I   : NatInductionRight L N)
(NS  : NatSuccNat L N.toIsNat N.toSucc)
(NA  : NatAddNat L N.toIsNat A)
(QEL : EqNatLeftEuc L N.toIsNat Q)
(QtS : EqNatToEqSucc L N.toIsNat Q N.toSucc)  
(A0C : AddNatZeroComm L N.toIsNat Q A N.toZero)
(ASn : AddSuccNatEqSucc L N.toIsNat Q A N.toSucc)
(AnS : AddNatSuccEqSucc L N.toIsNat Q A N.toSucc)
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

instance iAddNatComm 
{P : Sort u} {T : Type v} {L : Logic P} 
[N : PNat P T] [Q : LEq P T] [A : Add T]
[I   : NatInductionRight L N]
[NS  : NatSuccNat L N.toIsNat N.toSucc]
[NA  : NatAddNat L N.toIsNat A]
[QEL : EqNatLeftEuc L N.toIsNat Q]
[QtS : EqNatToEqSucc L N.toIsNat Q N.toSucc]  
[A0C : AddNatZeroComm L N.toIsNat Q A N.toZero]
[ASn : AddSuccNatEqSucc L N.toIsNat Q A N.toSucc]
[AnS : AddNatSuccEqSucc L N.toIsNat Q A N.toSucc]
: AddNatComm L N.toIsNat Q A 
:= {addNatComm := addNatCommProof I NS NA QEL QtS A0C ASn AnS}

instance iAddNatCommByPeano 
{P : Sort u} {T : Type v} {L : Logic P} 
[N : PNat P T] [Q : LEq P T] [A : Add T] [FaN : MForallNat L N.toIsNat]
[I   : NatInduction L N]
[N0  : NatZero L N.toIsNat N.toZero]
[NS  : NatSuccNat L N.toIsNat N.toSucc]
[NQ  : NatEqNat L N.toIsNat Q]
[QSm : EqNatSymm L N.toIsNat Q]
[QTr : EqNatTrans L N.toIsNat Q]
[QtS : EqNatToEqSucc L N.toIsNat Q N.toSucc]
[An0 : AddNatZeroEqNat L N.toIsNat Q A N.toZero]
[AnS : AddNatSuccEqSucc L N.toIsNat Q A N.toSucc]
: AddNatComm L N.toIsNat Q A := 
{addNatComm := 
  addNatCommProof iNatInductionRightByForallNat 
    NS iNatAddNatByPeano iEqNatLeftEucOfLeftEucT QtS 
    iAddNatZeroCommByPeano iAddSuccNatEqSuccByPeano AnS}

--------------------------------------------------------------------------------
-- Substitutivity
--------------------------------------------------------------------------------

-- Left Addition
-- (a = b) -> (c + a = c + b)

def eqNatAddNatLeftProof
{P : Sort u} {T : Type v} {L : Logic P} 
{N : PNat P T} {Q : LEq P T} {A : Add T} (If : MIf L)
(I    : NatInductionRight3 L N)
(NS   : NatSuccNat L N.toIsNat N.toSucc)
(NA0n : NatAddZeroNat L N.toIsNat A N.toZero)
(NA   : NatAddNat L N.toIsNat A)
(QJ   : EqNatJoin L N.toIsNat Q)
(QtS  : EqNatToEqSucc L N.toIsNat Q N.toSucc)
(A0n  : AddZeroNatEqNat L N.toIsNat Q A N.toZero)
(ASn  : AddSuccNatEqSucc L N.toIsNat Q A N.toSucc)
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

instance iEqNatAddNatLeft
{P : Sort u} {T : Type v} {L : Logic P} 
[N : PNat P T] [Q : LEq P T] [A : Add T] [If : MIf L]
[I    : NatInductionRight3 L N]
[NS   : NatSuccNat L N.toIsNat N.toSucc]
[QJ   : EqNatJoin L N.toIsNat Q] 
[QtS  : EqNatToEqSucc L N.toIsNat Q N.toSucc]
[NA   : NatAddNat L N.toIsNat A]
[NA0n : NatAddZeroNat L N.toIsNat A N.toZero]
[A0n  : AddZeroNatEqNat L N.toIsNat Q A N.toZero]
[ASn  : AddSuccNatEqSucc L N.toIsNat Q A N.toSucc]
: EqNatAddNatLeft L N.toIsNat Q A
:= {eqNatAddNatLeft := eqNatAddNatLeftProof If I NS NA0n NA QJ QtS A0n ASn}

instance iEqNatAddNatLeftByPeano
{P : Sort u} {T : Type v} {L : Logic P} 
[N : PNat P T] [Q : LEq P T] [A : Add T] 
[FaN : MForallNat L N.toIsNat] [If : MIf L]
[I   : NatInduction L N]
[N0  : NatZero L N.toIsNat N.toZero]
[NS  : NatSuccNat L N.toIsNat N.toSucc]
[NQ  : NatEqNat L N.toIsNat Q]
[QSm : EqNatSymm L N.toIsNat Q]
[QTr : EqNatTrans L N.toIsNat Q]
[QtS : EqNatToEqSucc L N.toIsNat Q N.toSucc]
[An0 : AddNatZeroEqNat L N.toIsNat Q A N.toZero]
[AnS : AddNatSuccEqSucc L N.toIsNat Q A N.toSucc]
: EqNatAddNatLeft L N.toIsNat Q A := 
{eqNatAddNatLeft := 
  eqNatAddNatLeftProof If iNatInductionRight3ByForallNat 
    NS iNatAddZeroNatByNatAdd iNatAddNatByPeano iEqNatJoinOfEqJoinT QtS 
    iAddZeroNatEqNatByPeano iAddSuccNatEqSuccByPeano}

-- Right Addition
-- (a = b) -> (a + c = b + c)

def eqNatAddNatRightProof
{P : Sort u} {T : Type v} {L : Logic P} 
{N : PNat P T} {Q : LEq P T} {A : Add T} (If : MIf L)
(I    : NatInductionRight3 L N)
(NS   : NatSuccNat L N.toIsNat N.toSucc)
(NAn0 : NatAddNatZero L N.toIsNat A N.toZero)
(NA   : NatAddNat L N.toIsNat A)
(QJ   : EqNatJoin L N.toIsNat Q)
(QtS  : EqNatToEqSucc L N.toIsNat Q N.toSucc)
(An0  : AddNatZeroEqNat L N.toIsNat Q A N.toZero)
(AnS  : AddNatSuccEqSucc L N.toIsNat Q A N.toSucc)
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

instance iEqNatAddNatRight 
{P : Sort u} {T : Type v} {L : Logic P} 
[N : PNat P T] [Q : LEq P T] [A : Add T] [If : MIf L]
[I    : NatInductionRight3 L N]
[NS   : NatSuccNat L N.toIsNat N.toSucc]
[QJ   : EqNatJoin L N.toIsNat Q] 
[QtS  : EqNatToEqSucc L N.toIsNat Q N.toSucc]
[NA   : NatAddNat L N.toIsNat A]
[NAn0 : NatAddNatZero L N.toIsNat A N.toZero]
[An0  : AddNatZeroEqNat L N.toIsNat Q A N.toZero]
[AnS  : AddNatSuccEqSucc L N.toIsNat Q A N.toSucc]
: EqNatAddNatRight L N.toIsNat Q A
:= {eqNatAddNatRight := eqNatAddNatRightProof If I NS NAn0 NA QJ QtS An0 AnS}

instance iEqNatAddNatRightByPeano
{P : Sort u} {T : Type v} {L : Logic P} 
[N : PNat P T] [Q : LEq P T] [A : Add T] 
[FaN : MForallNat L N.toIsNat] [If : MIf L]
[I   : NatInduction L N]
[N0  : NatZero L N.toIsNat N.toZero]
[NS  : NatSuccNat L N.toIsNat N.toSucc]
[NQ  : NatEqNat L N.toIsNat Q]
[QSm : EqNatSymm L N.toIsNat Q]
[QTr : EqNatTrans L N.toIsNat Q]
[QtS : EqNatToEqSucc L N.toIsNat Q N.toSucc]
[An0 : AddNatZeroEqNat L N.toIsNat Q A N.toZero]
[AnS : AddNatSuccEqSucc L N.toIsNat Q A N.toSucc]
: EqNatAddNatRight L N.toIsNat Q A := 
{eqNatAddNatRight := eqNatAddNatRightProof If iNatInductionRight3ByForallNat NS 
  iNatAddNatZeroByAddNatZero iNatAddNatByPeano iEqNatJoinOfEqJoinT QtS An0 AnS} 

--------------------------------------------------------------------------------
-- Associativity
--------------------------------------------------------------------------------

-- (a + b) + c = a + (b + c)

def addNatAssocByAddNatX 
{P : Sort u} {T : Type v} {L : Logic P} 
{N : PNat P T} {Q : LEq P T} {A : Add T}
(I    : NatInductionRight3 L N)
(NS   : NatSuccNat L N.toIsNat N.toSucc)
(NAn0 : NatAddNatZero L N.toIsNat A N.toZero)
(NA   : NatAddNat L N.toIsNat A)
(QTr  : EqNatTrans L N.toIsNat Q)
(QEL  : EqNatLeftEuc L N.toIsNat Q)
(QtS  : EqNatToEqSucc L N.toIsNat Q N.toSucc)
(QAL  : EqNatAddNatLeft L N.toIsNat Q A)
(An0  : AddNatZeroEqNat L N.toIsNat Q A N.toZero)
(AnS  : AddNatSuccEqSucc L N.toIsNat Q A N.toSucc)
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

instance iAddNatAssocByAddNatX 
{P : Sort u} {T : Type v} {L : Logic P} 
[N : PNat P T] [Q : LEq P T] [A : Add T]
[I    : NatInductionRight3 L N]
[NS   : NatSuccNat L N.toIsNat N.toSucc]
[NAn0 : NatAddNatZero L N.toIsNat A N.toZero]
[NA   : NatAddNat L N.toIsNat A]
[QTr  : EqNatTrans L N.toIsNat Q] 
[QEL  : EqNatLeftEuc L N.toIsNat Q]
[QtS  : EqNatToEqSucc L N.toIsNat Q N.toSucc]
[QAL  : EqNatAddNatLeft L N.toIsNat Q A]
[An0  : AddNatZeroEqNat L N.toIsNat Q A N.toZero]
[AnS  : AddNatSuccEqSucc L N.toIsNat Q A N.toSucc]
: AddNatAssoc L N.toIsNat Q A := 
{addNatAssoc := addNatAssocByAddNatX I NS NAn0 NA QTr QEL QtS QAL An0 AnS}

instance iAddNatAssocByPeano
{P : Sort u} {T : Type v} {L : Logic P} 
[N : PNat P T] [Q : LEq P T] [A : Add T] 
[FaN : MForallNat L N.toIsNat] [If : MIf L]
[NatInduction L N]
[N0  : NatZero L N.toIsNat N.toZero]
[NS  : NatSuccNat L N.toIsNat N.toSucc]
[NQ  : NatEqNat L N.toIsNat Q]
[QSm : EqNatSymm L N.toIsNat Q]
[QTr : EqNatTrans L N.toIsNat Q] 
[QtS : EqNatToEqSucc L N.toIsNat Q N.toSucc]
[An0 : AddNatZeroEqNat L N.toIsNat Q A N.toZero]
[AnS : AddNatSuccEqSucc L N.toIsNat Q A N.toSucc]
: AddNatAssoc L N.toIsNat Q A :=
{addNatAssoc := 
  addNatAssocByAddNatX iNatInductionRight3ByForallNat 
    NS iNatAddNatZeroByAddNatZero iNatAddNatByPeano 
    QTr iEqNatLeftEucOfLeftEucT QtS iEqNatAddNatLeftByPeano An0 AnS}

-- a + (b + c) = (a + b) + c 

def addNatAssocRevByAddNatX 
{P : Sort u} {T : Type v} {L : Logic P} 
{N : PNat P T} {Q : LEq P T} {A : Add T}
(I    : NatInductionRight3 L N)
(NS   : NatSuccNat L N.toIsNat N.toSucc)
(NAn0 : NatAddNatZero L N.toIsNat A N.toZero)
(NA   : NatAddNat L N.toIsNat A)
(QTr  : EqNatTrans L N.toIsNat Q)
(QEL  : EqNatLeftEuc L N.toIsNat Q)
(QtS  : EqNatToEqSucc L N.toIsNat Q N.toSucc)
(QAL  : EqNatAddNatLeft L N.toIsNat Q A)
(An0  : AddNatZeroEqNat L N.toIsNat Q A N.toZero)
(AnS  : AddNatSuccEqSucc L N.toIsNat Q A N.toSucc)
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

instance iAddNatAssocRevByAddNatX
{P : Sort u} {T : Type v} {L : Logic P} 
[N : PNat P T] [Q : LEq P T] [A : Add T]
[I   : NatInductionRight3 L N]
[NS  : NatSuccNat L N.toIsNat N.toSucc]
[NAn0 : NatAddNatZero L N.toIsNat A N.toZero]
[NA  : NatAddNat L N.toIsNat A]
[QTr : EqNatTrans L N.toIsNat Q] 
[QEL : EqNatLeftEuc L N.toIsNat Q]
[QtS : EqNatToEqSucc L N.toIsNat Q N.toSucc]
[QAL : EqNatAddNatLeft L N.toIsNat Q A]
[An0 : AddNatZeroEqNat L N.toIsNat Q A N.toZero]
[AnS : AddNatSuccEqSucc L N.toIsNat Q A N.toSucc]
: AddNatAssocRev L N.toIsNat Q A := 
{addNatAssocRev := addNatAssocRevByAddNatX I NS NAn0 NA QTr QEL QtS QAL An0 AnS}

instance iAddNatAssocRevByPeano 
{P : Sort u} {T : Type v} {L : Logic P} 
[N : PNat P T] [Q : LEq P T] [A : Add T] 
[FaN : MForallNat L N.toIsNat] [If : MIf L]
[I   : NatInduction L N]
[N0  : NatZero L N.toIsNat N.toZero]
[NS  : NatSuccNat L N.toIsNat N.toSucc]
[NQ  : NatEqNat L N.toIsNat Q]
[QSm : EqNatSymm L N.toIsNat Q]
[QTr : EqNatTrans L N.toIsNat Q] 
[QtS : EqNatToEqSucc L N.toIsNat Q N.toSucc]
[An0 : AddNatZeroEqNat L N.toIsNat Q A N.toZero]
[AnS : AddNatSuccEqSucc L N.toIsNat Q A N.toSucc]
: AddNatAssocRev L N.toIsNat Q A := 
{addNatAssocRev := 
  addNatAssocRevByAddNatX iNatInductionRight3ByForallNat 
    NS iNatAddNatZeroByAddNatZero iNatAddNatByPeano 
    QTr iEqNatLeftEucOfLeftEucT QtS iEqNatAddNatLeftByPeano An0 AnS}

--------------------------------------------------------------------------------
-- Special Cases
--------------------------------------------------------------------------------

-- a + 1 = S a

def addNatOneEqSuccByNatAdd
{P : Sort u} {T : Type v} {L : Logic P}
{N : IsNat P T} {Q : LEq P T} {A : Add T} {Z : Zero T} {O : One T} {Su : Succ T} 
(N0  : NatZero L N Z)
(N1  : NatOne L N O)
(NS  : NatSuccNat L N Su)
(NA  : NatAddNat L N A)
(QTr : EqNatTrans L N Q)
(QtS : EqNatToEqSucc L N Q Su)
(Q1S : OneEqSuccZero L Q Z O Su)
(QAL : EqNatAddNatLeft L N Q A)  
(An0 : AddNatZeroEqNat L N Q A Z)
(AnS : AddNatSuccEqSucc L N Q A Su)
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
{P : Sort u} {T : Type v} {L : Logic P}
[N : IsNat P T] [Q : LEq P T] [A : Add T] [Z : Zero T] [O : One T] [Su : Succ T] 
[N0  : NatZero L N Z]
[N1  : NatOne L N O]
[NS  : NatSuccNat L N Su]
[NA  : NatAddNat L N A]
[QTr : EqNatTrans L N Q]
[QtS : EqNatToEqSucc L N Q Su]
[Q1S : OneEqSuccZero L Q Z O Su]
[QAL : EqNatAddNatLeft L N Q A] 
[An0 : AddNatZeroEqNat L N Q A Z]
[AnS : AddNatSuccEqSucc L N Q A Su] 
: AddNatOneEqSucc L N Q A O Su
:= {addNatOneEqSucc := addNatOneEqSuccByNatAdd N0 N1 NS NA QTr QtS Q1S QAL An0 AnS}

def addNatOneEqSuccByNatEq
{P : Sort u} {T : Type v} {L : Logic P}
{N : IsNat P T} {Q : LEq P T} {A : Add T} {Z : Zero T} {O : One T} {Su : Succ T} 
(N0  : NatZero L N Z)
(NS  : NatSuccNat L N Su)
(NQ  : NatEqNat L N Q)
(QTr : EqNatTrans L N Q)
(QtS : EqNatToEqSucc L N Q Su)
(Q1S : OneEqSuccZero L Q Z O Su)
(QAL : EqNatAddNatLeft L N Q A) 
(An0 : AddNatZeroEqNat L N Q A Z)
(AnS : AddNatSuccEqSucc L N Q A Su)
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
{P : Sort u} {T : Type v} {L : Logic P}
[N : IsNat P T] [Q : LEq P T] [A : Add T] [Z : Zero T] [O : One T] [Su : Succ T] 
[N0  : NatZero L N Z]
[NS  : NatSuccNat L N Su]
[NQ  : NatEqNat L N Q]
[QTr : EqNatTrans L N Q]
[QtS : EqNatToEqSucc L N Q Su]
[Q1S : OneEqSuccZero L Q Z O Su] 
[QAL : EqNatAddNatLeft L N Q A] 
[An0 : AddNatZeroEqNat L N Q A Z]
[AnS : AddNatSuccEqSucc L N Q A Su]
: AddNatOneEqSucc L N Q A O Su
:= {addNatOneEqSucc := addNatOneEqSuccByNatEq N0 NS NQ QTr QtS Q1S QAL An0 AnS}

-- 1 + a = S a

def addOneNatEqSuccByNatAdd
{P : Sort u} {T : Type v} {L : Logic P}
{N : IsNat P T} {Q : LEq P T} {A : Add T} {Z : Zero T} {O : One T} {Su : Succ T} 
(N0  : NatZero L N Z)
(N1  : NatOne L N O)
(NS  : NatSuccNat L N Su)
(NA  : NatAddNat L N A)
(QTr : EqNatTrans L N Q)
(QtS : EqNatToEqSucc L N Q Su)
(Q1S : OneEqSuccZero L Q Z O Su)
(QAR : EqNatAddNatRight L N Q A)  
(A0n : AddZeroNatEqNat L N Q A Z)
(ASn : AddSuccNatEqSucc L N Q A Su)
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
{P : Sort u} {T : Type v} {L : Logic P}
[N : IsNat P T] [Q : LEq P T] [A : Add T] [Z : Zero T] [O : One T] [Su : Succ T] 
[N0  : NatZero L N Z]
[N1  : NatOne L N O]
[NS  : NatSuccNat L N Su]
[NA  : NatAddNat L N A]
[QTr : EqNatTrans L N Q]
[QtS : EqNatToEqSucc L N Q Su]
[Q1S : OneEqSuccZero L Q Z O Su]
[QAR : EqNatAddNatRight L N Q A]
[A0n : AddZeroNatEqNat L N Q A Z]
[ASn : AddSuccNatEqSucc L N Q A Su]
: AddOneNatEqSucc L N Q A O Su := 
  {addOneNatEqSucc := 
    addOneNatEqSuccByNatAdd N0 N1 NS NA QTr QtS Q1S QAR A0n ASn}

end Gaea.Peano