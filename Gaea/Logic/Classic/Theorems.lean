import Gaea.Logic.Basic.Rules
import Gaea.Logic.Classic.Rules

namespace Gaea.Logic

universe u
variable {P : Sort u}


--------------------------------------------------------------------------------
-- Contrapositive
--------------------------------------------------------------------------------

-- (~q |- ~p) |- (p -> q)

def contraIfIntroByIfDneNot 
{L : Logic P} {If : LIf P} {Nt : LNot P}
(IfI : IfIntro L If) 
(DnE : DblNegElim L Nt)
(ByC : ByContradiction L Nt)
: (p q : P) -> ((L |- ~q) -> (L |- ~p)) -> (L |- p -> q)
:= by
  intro p q Nq_to_Np
  apply ifIntro; intro Lp
  apply dblNegElim
  apply byContradiction; intro LNq
  have LNp := Nq_to_Np LNq
  exact contradiction Lp LNp

instance iContraIfIntroByIfDneNot
{L : Logic P} [If : LIf P] [Nt : LNot P]
[IfI : IfIntro L If]
[DnE : DblNegElim L Nt]
[ByC : ByContradiction L Nt]
: ContraIfIntro L If Nt :=
{contraIfIntro := contraIfIntroByIfDneNot IfI DnE ByC}

-- (p -> q) |- (~q |- ~p) 

def contraIfElimByIfNot 
{L : Logic P} {If : LIf P} {Nt : LNot P}
(IfE : IfElim L If) 
(ByC : ByContradiction L Nt)
: (p q : P) -> (L |- p -> q) -> (L |- ~q) -> (L |- ~p)
:= by
  intro p q LpTq LNq
  apply byContradiction; intro Lp
  have Lq := ifElim LpTq Lp
  exact contradiction Lq LNq

instance iContraIfElimByIfNot 
{L : Logic P} [If : LIf P] [Nt : LNot P]
[IfE : IfElim L If]
[ByC : ByContradiction L Nt]
: ContraIfElim L If Nt :=
{contraIfElim := contraIfElimByIfNot IfE ByC}

--------------------------------------------------------------------------------
-- Modus Ponens
--------------------------------------------------------------------------------

def mpByIfConj {L : Logic P} {If : LIf P} {Cj : Conj P} 
(IfE : IfElim L If) (CjU : ConjUncurry L Cj)
: (p q : P) -> (L |- (p -> q) /\ p) -> (L |- q)
:= by
  intro p q
  apply conjUncurry
  intro LpTq Lp
  exact ifElim LpTq Lp

instance iMpByIfConj {L : Logic P} [If : LIf P] [Cj : Conj P] 
[IfE : IfElim L If] [CjU : ConjUncurry L Cj]
: ModusPonens L If Cj := {mp := mpByIfConj IfE CjU}

--------------------------------------------------------------------------------
-- Modus Tollens
--------------------------------------------------------------------------------

def mtByContraIfConj {L : Logic P} 
{If : LIf P} {Cj : Conj P} {Nt : LNot P}
(CjU : ConjUncurry L Cj)
(CfE : ContraIfElim L If Nt)
: (p q : P) -> (L |- (p -> q) /\ ~q) -> (L |- ~p)
:= by
  intro p q
  apply conjUncurry
  intro LpTq LNq
  exact contraIfElim LpTq LNq

instance iMtByContraIfConj {L : Logic P} 
[If : LIf P] [Cj : Conj P] [Nt : LNot P]
[CjU : ConjUncurry L Cj]
[CfE : ContraIfElim L If Nt]
: ModusTollens L If Cj Nt :=
{mt := mtByContraIfConj CjU CfE}

--------------------------------------------------------------------------------
-- Syllogisms
--------------------------------------------------------------------------------

def hypoSylByIfConj {L : Logic P}
{If : LIf P} {Cj : Conj P}
(IfI : IfIntro L If) 
(IfE : IfElim L If) 
(CjU : ConjUncurry L Cj) 
: (p q r : P) -> (L |- (p -> q) /\ (q -> r)) -> (L |- p -> r)
:= by
  intro p q r 
  apply conjUncurry 
  intro LpTq LqTr
  apply ifIntro; intro Lp
  have Lq := ifElim LpTq Lp
  have Lr := ifElim LqTr Lq 
  exact Lr

instance iHypoSylByIfConj {L : Logic P} 
[If : LIf P] [Cj : Conj P]
[IfI : IfIntro L If] 
[IfE : IfElim L If]
[CjU : ConjUncurry L Cj]
: HypoSyl L If Cj :=
{hypoSyl := hypoSylByIfConj IfI IfE CjU}

def disjSylByConjDisjNot {L : Logic P} 
{Cj : Conj P} {Dj : Disj P} {Nt : LNot P}
(CjU : ConjUncurry L Cj) 
(DeL : DisjElimLeft L Dj Nt)
: (p q : P) -> (L |- (p \/ q) /\ ~p) -> (L |- q)
:= by
  intro p q
  apply conjUncurry
  intro LpDq LNp
  exact disjElimLeft LpDq LNp

instance iDisjSylByConjDisjNot {L : Logic P} 
[Cj : Conj P] [Dj : Disj P] [Nt : LNot P] 
[CjU : ConjUncurry L Cj]
[DeL : DisjElimLeft L Dj Nt]
: DisjSyl L Cj Dj Nt :=
{disjSyl := disjSylByConjDisjNot CjU DeL}

--------------------------------------------------------------------------------
-- Dilemmas
--------------------------------------------------------------------------------

-- Constructive Dilemma
-- (p -> q) /\ (r -> s) /\ (p \/ r) |- q \/ s 

def cnstrDilByIfConjDisj {L : Logic P} 
{If : LIf P} {Cj : Conj P} {Dj : Disj P}
(IfE : IfElim L If) 
(CjU : ConjUncurry L Cj) 
(DiL : DisjIntroLeft L Dj)
(DiR : DisjIntroRight L Dj) 
(DjE : DisjElim L Dj)
: (p q r s : P) -> 
    (L |- (p -> q) /\ (r -> s) /\ (p \/ r)) -> (L |- q \/ s) 
:= by
  intro p q r s
  apply conjUncurry; intro LpTq
  apply conjUncurry; intro LrTs LpDr
  apply disjElim LpDr ?pTqDs ?rTqDs
  case pTqDs =>
    intro Lp
    apply disjIntroLeft
    exact ifElim LpTq Lp
  case rTqDs =>
    intro Lr
    apply disjIntroRight
    exact ifElim LrTs Lr

instance iCnstrDilByIfConjDisj {L : Logic P} 
[If : LIf P] [Cj : Conj P] [Dj : Disj P]
[IfE : IfElim L If]
[CjU : ConjUncurry L Cj]
[DiL : DisjIntroLeft L Dj]
[DiR : DisjIntroRight L Dj] 
[DjE : DisjElim L Dj]
: CnstrDil L If Cj Dj :=
{cnstrDil := cnstrDilByIfConjDisj IfE CjU DiL DiR DjE} 

-- Destructive Dilemma
-- (p -> q) /\ (r -> s) /\ (~q \/ ~s) |- ~p \/ ~r 

def destrDilByIfConjDisj {L : Logic P} 
{If : LIf P} {Cj : Conj P} {Dj : Disj P} {Nt : LNot P}
(CfE : ContraIfElim L If Nt)
(CjU : ConjUncurry L Cj) 
(DiL : DisjIntroLeft L Dj)
(DiR : DisjIntroRight L Dj) 
(DjE : DisjElim L Dj)
: (p q r s : P) -> 
    (L |- (p -> q) /\ (r -> s) /\ (~q \/ ~s)) -> (L |- ~p \/ ~r) 
:= by
  intro p q r s
  apply conjUncurry; intro LpTq
  apply conjUncurry; intro LrTs LNqDNs
  apply disjElim LNqDNs ?NqTNpDNr ?NsTNpDNr
  case NqTNpDNr =>
    intro LNq
    apply disjIntroLeft
    exact contraIfElim LpTq LNq
  case NsTNpDNr =>
    intro LNs
    apply disjIntroRight
    exact contraIfElim LrTs LNs

instance iDestrDilByIfConjDisj {L : Logic P} 
[If : LIf P] [Cj : Conj P] [Dj : Disj P] [Nt : LNot P]
[CfE : ContraIfElim L If Nt]
[CjU : ConjUncurry L Cj]
[DiL : DisjIntroLeft L Dj]
[DiR : DisjIntroRight L Dj] 
[DjE : DisjElim L Dj]
: DestrDil L If Cj Dj Nt :=
{destrDil := destrDilByIfConjDisj CfE CjU DiL DiR DjE } 

-- Bidirectional Dilemma
-- (p -> q) /\ (r -> s) /\ (p \/ ~s) |- q \/ ~r 

def bidirDilByIfConjDisj {L : Logic P} 
{If : LIf P} {Cj : Conj P} {Dj : Disj P} {Nt : LNot P}
(IfE : IfElim L If) 
(CfE : ContraIfElim L If Nt)
(CjU : ConjUncurry L Cj)
(DiL : DisjIntroLeft L Dj)
(DiR : DisjIntroRight L Dj) 
(DjE : DisjElim L Dj)
: (p q r s : P) -> 
    (L |- (p -> q) /\ (r -> s) /\ (p \/ ~s)) -> (L |- q \/ ~r) 
:= by
  intro p q r s
  apply conjUncurry; intro LpTq
  apply conjUncurry; intro LrTs LpDNs
  apply disjElim LpDNs ?pTqDNr ?NsTqDNr
  case pTqDNr =>
    intro Lp
    apply disjIntroLeft
    exact ifElim LpTq Lp
  case NsTqDNr =>
    intro LNs
    apply disjIntroRight
    exact contraIfElim LrTs LNs

instance iBidirDilByIfConjDisj {L : Logic P} 
[If : LIf P] [Cj : Conj P] [Dj : Disj P] [Nt : LNot P]
[IfE : IfElim L If]
[CjU : ConjUncurry L Cj]
[DiL : DisjIntroLeft L Dj]
[DiR : DisjIntroRight L Dj] 
[DjE : DisjElim L Dj]
[CfE : ContraIfElim L If Nt]
: BidirDil L If Cj Dj Nt :=
{bidirDil := bidirDilByIfConjDisj IfE CfE CjU DiL DiR DjE} 

end Gaea.Logic
