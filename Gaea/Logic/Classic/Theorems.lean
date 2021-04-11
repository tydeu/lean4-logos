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
(Mp : ModusPonens L Im.imp) (CjU : Uncurry L Cj.conj)
: (p q : P) -> (L |- (p -> q) /\ p) -> (L |- q)
:= by
  intro p q
  assume (LpTq, Lp)
  mp LpTq Lp

instance iConjMpByIfConj {L : Logic P} [Im : Imp P] [Cj : Conj P] 
[Mp : ModusPonens L Im.imp] [CjU : Uncurry L Cj.conj]
: ConjMp L Im Cj := {conjMp := conjMpByIfConj Mp CjU}

--------------------------------------------------------------------------------
-- Modus Tollens
--------------------------------------------------------------------------------

def conjMtByContraIfConj {L : Logic P} 
{Im : Imp P} {Cj : Conj P} {Nt : LNot P}
(CjU : Uncurry L Cj.conj)
(Mt  : ModusTollens L Im.imp Nt.not)
: (p q : P) -> (L |- (p -> q) /\ ~q) -> (L |- ~p)
:= by
  intro p q
  assume (LpTq, LNq)
  mt LpTq LNq

instance iConjMtByContraIfConj {L : Logic P} 
[Im : Imp P] [Cj : Conj P] [Nt : LNot P]
[CjU : Uncurry L Cj.conj]
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
(CjU : Uncurry L Cj.conj) 
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
[CjU : Uncurry L Cj.conj]
: HypoSyl L Im Cj :=
{hypoSyl := hypoSylByIfConj Mp ByI CjU}

def disjSylByConjDisjNot {L : Logic P} 
{Cj : Conj P} {Dj : Disj P} {Nt : LNot P}
(CjU : Uncurry L Cj.conj) 
(DeL : LeftNeg L Dj.disj Nt.not)
: (p q : P) -> (L |- (p \/ q) /\ ~p) -> (L |- q)
:= by
  intro p q
  assume (LpDq, LNp)
  exact leftNeg LpDq LNp

instance iDisjSylByConjDisjNot {L : Logic P} 
[Cj : Conj P] [Dj : Disj P] [Nt : LNot P] 
[CjU : Uncurry L Cj.conj]
[DeL : LeftNeg L Dj.disj Nt.not]
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
(CjU : Uncurry L Cj.conj) 
(DiL : LeftTaut L Dj.disj)
(DiR : RightTaut L Dj.disj) 
(DjE : ByEither L Dj.disj)
: (p q r s : P) -> 
    (L |- (p -> q) /\ (r -> s) /\ (p \/ r)) -> (L |- q \/ s) 
:= by
  intro p q r s
  assume (LpTq, LrTs, LpDr)
  apply byEither LpDr ?pTqDs ?rTqDs
  case pTqDs =>
    intro Lp
    apply leftTaut
    mp LpTq Lp
  case rTqDs =>
    intro Lr
    apply rightTaut
    mp LrTs Lr

instance iCnstrDilByIfConjDisj {L : Logic P} 
[Im : Imp P] [Cj : Conj P] [Dj : Disj P]
[Mp  : ModusPonens L Im.imp]
[CjU : Uncurry L Cj.conj]
[DiL : LeftTaut L Dj.disj]
[DiR : RightTaut L Dj.disj] 
[DjE : ByEither L Dj.disj]
: CnstrDil L Im Cj Dj :=
{cnstrDil := cnstrDilByIfConjDisj Mp CjU DiL DiR DjE} 

-- Destructive Dilemma
-- (p -> q) /\ (r -> s) /\ (~q \/ ~s) |- ~p \/ ~r 

def destrDilByIfConjDisj {L : Logic P} 
{Im : Imp P} {Cj : Conj P} {Dj : Disj P} {Nt : LNot P}
(Mt : ModusTollens L Im.imp Nt.not)
(CjU : Uncurry L Cj.conj) 
(DiL : LeftTaut L Dj.disj)
(DiR : RightTaut L Dj.disj) 
(DjE : ByEither L Dj.disj)
: (p q r s : P) -> 
    (L |- (p -> q) /\ (r -> s) /\ (~q \/ ~s)) -> (L |- ~p \/ ~r) 
:= by
  intro p q r s
  assume (LpTq, LrTs, LNqDNs)
  apply byEither LNqDNs ?NqTNpDNr ?NsTNpDNr
  case NqTNpDNr =>
    intro LNq
    apply leftTaut
    mt LpTq LNq
  case NsTNpDNr =>
    intro LNs
    apply rightTaut
    mt LrTs LNs

instance iDestrDilByIfConjDisj {L : Logic P} 
[Im : Imp P] [Cj : Conj P] [Dj : Disj P] [Nt : LNot P]
[Mt : ModusTollens L Im.imp Nt.not]
[CjU : Uncurry L Cj.conj]
[DiL : LeftTaut L Dj.disj]
[DiR : RightTaut L Dj.disj] 
[DjE : ByEither L Dj.disj]
: DestrDil L Im Cj Dj Nt :=
{destrDil := destrDilByIfConjDisj Mt CjU DiL DiR DjE } 

-- Bidirectional Dilemma
-- (p -> q) /\ (r -> s) /\ (p \/ ~s) |- q \/ ~r 

def bidirDilByIfConjDisj {L : Logic P} 
{Im : Imp P} {Cj : Conj P} {Dj : Disj P} {Nt : LNot P}
(Mp  : ModusPonens L Im.imp) 
(Mt  : ModusTollens L Im.imp Nt.not)
(CjU : Uncurry L Cj.conj)
(DiL : LeftTaut L Dj.disj)
(DiR : RightTaut L Dj.disj) 
(DjE : ByEither L Dj.disj)
: (p q r s : P) -> 
    (L |- (p -> q) /\ (r -> s) /\ (p \/ ~s)) -> (L |- q \/ ~r) 
:= by
  intro p q r s
  assume (LpTq, LrTs, LpDNs)
  apply byEither LpDNs ?pTqDNr ?NsTqDNr
  case pTqDNr =>
    intro Lp
    apply leftTaut
    mp LpTq Lp
  case NsTqDNr =>
    intro LNs
    apply rightTaut
    mt LrTs LNs

instance iBidirDilByIfConjDisj {L : Logic P} 
[Im : Imp P] [Cj : Conj P] [Dj : Disj P] [Nt : LNot P]
[Mp  : ModusPonens L Im.imp]
[Mt  : ModusTollens L Im.imp Nt.not]
[CjU : Uncurry L Cj.conj]
[DiL : LeftTaut L Dj.disj]
[DiR : RightTaut L Dj.disj] 
[DjE : ByEither L Dj.disj]
: BidirDil L Im Cj Dj Nt :=
{bidirDil := bidirDilByIfConjDisj Mp Mt CjU DiL DiR DjE} 

end Gaea.Logic
