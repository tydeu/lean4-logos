import Gaea.Logic.Prop.Rules
import Gaea.Logic.Prop.Tactics
import Gaea.Logic.Classic.Rules

namespace Gaea.Logic

universe u
variable {P : Sort u}

--------------------------------------------------------------------------------
-- Modus Ponens
--------------------------------------------------------------------------------

def conjMpByIfConj {L : Logic P} {Im : Imp P} {Cj : Conj P} 
(Mp : ModusPonens L Im.imp) (CjU : ConjUncurry L Cj)
: (p q : P) -> (L |- (p -> q) /\ p) -> (L |- q)
:= by
  intro p q
  assume (LpTq, Lp)
  mp LpTq Lp

instance iConjMpByIfConj {L : Logic P} [Im : Imp P] [Cj : Conj P] 
[Mp : ModusPonens L Im.imp] [CjU : ConjUncurry L Cj]
: ConjMp L Im Cj := {conjMp := conjMpByIfConj Mp CjU}

--------------------------------------------------------------------------------
-- Modus Tollens
--------------------------------------------------------------------------------

def conjMtByContraIfConj {L : Logic P} 
{Im : Imp P} {Cj : Conj P} {Nt : LNot P}
(CjU : ConjUncurry L Cj)
(Mt  : ModusTollens L Im.imp Nt.not)
: (p q : P) -> (L |- (p -> q) /\ ~q) -> (L |- ~p)
:= by
  intro p q
  assume (LpTq, LNq)
  mt LpTq LNq

instance iConjMtByContraIfConj {L : Logic P} 
[Im : Imp P] [Cj : Conj P] [Nt : LNot P]
[CjU : ConjUncurry L Cj]
[Mt  : ModusTollens L Im.imp Nt.not]
: ConjMt L Im Cj Nt :=
{conjMt := conjMtByContraIfConj CjU Mt}

--------------------------------------------------------------------------------
-- Syllogisms
--------------------------------------------------------------------------------

def hypoSylByIfConj {L : Logic P}
{Im : Imp P} {Cj : Conj P}
(Mp  : ModusPonens L Im.imp) 
(ByI : ByImplication L Im.imp) 
(CjU : ConjUncurry L Cj) 
: (p q r : P) -> (L |- (p -> q) /\ (q -> r)) -> (L |- p -> r)
:= by
  intro p q r 
  assume (LpTq, LqTr) 
  byImplication Lp
  have Lq := mp LpTq Lp
  have Lr := mp LqTr Lq 
  exact Lr

instance iHypoSylByIfConj {L : Logic P} 
[Im : Imp P] [Cj : Conj P]
[Mp  : ModusPonens L Im.imp]
[ByI : ByImplication L Im.imp] 
[CjU : ConjUncurry L Cj]
: HypoSyl L Im Cj :=
{hypoSyl := hypoSylByIfConj Mp ByI CjU}

def disjSylByConjDisjNot {L : Logic P} 
{Cj : Conj P} {Dj : Disj P} {Nt : LNot P}
(CjU : ConjUncurry L Cj) 
(DeL : DisjElimLeft L Dj Nt.not)
: (p q : P) -> (L |- (p \/ q) /\ ~p) -> (L |- q)
:= by
  intro p q
  assume (LpDq, LNp)
  exact disjElimLeft LpDq LNp

instance iDisjSylByConjDisjNot {L : Logic P} 
[Cj : Conj P] [Dj : Disj P] [Nt : LNot P] 
[CjU : ConjUncurry L Cj]
[DeL : DisjElimLeft L Dj Nt.not]
: DisjSyl L Cj Dj Nt :=
{disjSyl := disjSylByConjDisjNot CjU DeL}

--------------------------------------------------------------------------------
-- Dilemmas
--------------------------------------------------------------------------------

-- Constructive Dilemma
-- (p -> q) /\ (r -> s) /\ (p \/ r) |- q \/ s 

def cnstrDilByIfConjDisj {L : Logic P} 
{Im : Imp P} {Cj : Conj P} {Dj : Disj P}
(Mp  : ModusPonens L Im.imp) 
(CjU : ConjUncurry L Cj) 
(DiL : DisjIntroLeft L Dj)
(DiR : DisjIntroRight L Dj) 
(DjE : DisjElim L Dj)
: (p q r s : P) -> 
    (L |- (p -> q) /\ (r -> s) /\ (p \/ r)) -> (L |- q \/ s) 
:= by
  intro p q r s
  assume (LpTq, LrTs, LpDr)
  apply disjElim LpDr ?pTqDs ?rTqDs
  case pTqDs =>
    intro Lp
    apply disjIntroLeft
    mp LpTq Lp
  case rTqDs =>
    intro Lr
    apply disjIntroRight
    mp LrTs Lr

instance iCnstrDilByIfConjDisj {L : Logic P} 
[Im : Imp P] [Cj : Conj P] [Dj : Disj P]
[Mp  : ModusPonens L Im.imp]
[CjU : ConjUncurry L Cj]
[DiL : DisjIntroLeft L Dj]
[DiR : DisjIntroRight L Dj] 
[DjE : DisjElim L Dj]
: CnstrDil L Im Cj Dj :=
{cnstrDil := cnstrDilByIfConjDisj Mp CjU DiL DiR DjE} 

-- Destructive Dilemma
-- (p -> q) /\ (r -> s) /\ (~q \/ ~s) |- ~p \/ ~r 

def destrDilByIfConjDisj {L : Logic P} 
{Im : Imp P} {Cj : Conj P} {Dj : Disj P} {Nt : LNot P}
(Mt : ModusTollens L Im.imp Nt.not)
(CjU : ConjUncurry L Cj) 
(DiL : DisjIntroLeft L Dj)
(DiR : DisjIntroRight L Dj) 
(DjE : DisjElim L Dj)
: (p q r s : P) -> 
    (L |- (p -> q) /\ (r -> s) /\ (~q \/ ~s)) -> (L |- ~p \/ ~r) 
:= by
  intro p q r s
  assume (LpTq, LrTs, LNqDNs)
  apply disjElim LNqDNs ?NqTNpDNr ?NsTNpDNr
  case NqTNpDNr =>
    intro LNq
    apply disjIntroLeft
    mt LpTq LNq
  case NsTNpDNr =>
    intro LNs
    apply disjIntroRight
    mt LrTs LNs

instance iDestrDilByIfConjDisj {L : Logic P} 
[Im : Imp P] [Cj : Conj P] [Dj : Disj P] [Nt : LNot P]
[Mt : ModusTollens L Im.imp Nt.not]
[CjU : ConjUncurry L Cj]
[DiL : DisjIntroLeft L Dj]
[DiR : DisjIntroRight L Dj] 
[DjE : DisjElim L Dj]
: DestrDil L Im Cj Dj Nt :=
{destrDil := destrDilByIfConjDisj Mt CjU DiL DiR DjE } 

-- Bidirectional Dilemma
-- (p -> q) /\ (r -> s) /\ (p \/ ~s) |- q \/ ~r 

def bidirDilByIfConjDisj {L : Logic P} 
{Im : Imp P} {Cj : Conj P} {Dj : Disj P} {Nt : LNot P}
(Mp  : ModusPonens L Im.imp) 
(Mt  : ModusTollens L Im.imp Nt.not)
(CjU : ConjUncurry L Cj)
(DiL : DisjIntroLeft L Dj)
(DiR : DisjIntroRight L Dj) 
(DjE : DisjElim L Dj)
: (p q r s : P) -> 
    (L |- (p -> q) /\ (r -> s) /\ (p \/ ~s)) -> (L |- q \/ ~r) 
:= by
  intro p q r s
  assume (LpTq, LrTs, LpDNs)
  apply disjElim LpDNs ?pTqDNr ?NsTqDNr
  case pTqDNr =>
    intro Lp
    apply disjIntroLeft
    mp LpTq Lp
  case NsTqDNr =>
    intro LNs
    apply disjIntroRight
    mt LrTs LNs

instance iBidirDilByIfConjDisj {L : Logic P} 
[Im : Imp P] [Cj : Conj P] [Dj : Disj P] [Nt : LNot P]
[Mp  : ModusPonens L Im.imp]
[Mt  : ModusTollens L Im.imp Nt.not]
[CjU : ConjUncurry L Cj]
[DiL : DisjIntroLeft L Dj]
[DiR : DisjIntroRight L Dj] 
[DjE : DisjElim L Dj]
: BidirDil L Im Cj Dj Nt :=
{bidirDil := bidirDilByIfConjDisj Mp Mt CjU DiL DiR DjE} 

end Gaea.Logic
