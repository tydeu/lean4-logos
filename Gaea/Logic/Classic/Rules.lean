import Gaea.Logic.Notation

namespace Gaea.Logic

universe u
variable {P : Sort u} (L : Logic P)

-- Modus Ponens
-- (p -> q) /\ p |- q 

class ConjMp (Im : Imp P) (Cj : Conj P) :=
  conjMp : (p q : P) -> (L |- (p -> q) /\ p) -> (L |- q) 

def conjMp {L} [Im : Imp P] [Cj : Conj P] 
[K : ConjMp L Im Cj] {p q : P} := K.conjMp p q

-- Modus Tollens
-- (p -> q) /\ ~q |- ~p 

class ConjMt (Im : Imp P) (Cj : Conj P) (Nt : LNot P) :=
  conjMt : (p q : P) -> (L |- (p -> q) /\ ~q) -> (L |- ~p) 

def conjMt {L} [Im : Imp P] [Cj : Conj P] [Nt : LNot P]
[K : ConjMt L Im Cj Nt] {p q : P} := K.conjMt p q

-- Hypothetical Syllogism
-- (p -> q) /\ (q -> r) |- (p -> r) 

class HypoSyl (Im : Imp P) (Cj : Conj P) :=
  hypoSyl : (p q r : P) -> (L |- (p -> q) /\ (q -> r)) -> (L |- p -> r) 

def hypoSyl {L} [Im : Imp P] [Cj : Conj P] 
[K : HypoSyl L Im Cj] {p q r : P} := K.hypoSyl p q r

-- Disjunctive Syllogism
-- (p \/ q) /\ ~p |- q 

class DisjSyl (Cj : Conj P) (Dj : Disj P) (Nt : LNot P) :=
  disjSyl : (p q : P) -> (L |- (p \/ q) /\ ~p) -> (L |- q) 

def disjSyl {L} [Cj : Conj P] [Dj : Disj P] [Nt : LNot P]
[K : DisjSyl L Cj Dj Nt] {p q : P} := K.disjSyl p q

-- Constructive Dilemma
-- (p -> q) /\ (r -> s) /\ (p \/ r) |- q \/ s 

class CnstrDil (Im : Imp P) (Cj : Conj P) (Dj : Disj P) :=
  cnstrDil : (p q r s : P) -> 
    (L |- (p -> q) /\ (r -> s) /\ (p \/ r)) -> (L |- q \/ s) 

def cnstrDil {L} [Im : Imp P] [Cj : Conj P] [Dj : Disj P]
[K : CnstrDil L Im Cj Dj] {p q r s: P} := K.cnstrDil p q r s

-- Destructive Dilemma
-- (p -> q) /\ (r -> s) /\ (~q \/ ~s) |- ~p \/ ~r 

class DestrDil (Im : Imp P) (Cj : Conj P) (Dj : Disj P) (Nt : LNot P) :=
  destrDil : (p q r s : P) -> 
    (L |- (p -> q) /\ (r -> s) /\ (~q \/ ~s)) -> (L |- ~p \/ ~r) 

def destrDil {L} [Im : Imp P] [Cj : Conj P] [Dj : Disj P] [Nt : LNot P]
[K : DestrDil L Im Cj Dj Nt] {p q r s: P} := K.destrDil p q r s

-- Bidirectional Dilemma
-- (p -> q) /\ (r -> s) /\ (p \/ ~s) |- q \/ ~r 

class BidirDil (Im : Imp P) (Cj : Conj P) (Dj : Disj P) (Nt : LNot P) :=
  bidirDil : (p q r s : P) -> 
    (L |- (p -> q) /\ (r -> s) /\ (p \/ ~s)) -> (L |- q \/ ~r) 

def bidirDil {L} [Im : Imp P] [Cj : Conj P] [Dj : Disj P] [Nt : LNot P]
[K : BidirDil L Im Cj Dj Nt] {p q r s: P} := K.bidirDil p q r s

-- Composition
-- (p -> q) /\ (p -> r) |- p -> (q /\ r)

class Composition (Im : Imp P) (Cj : Conj P) :=
  composition : (p q r : P) -> (L |- (p -> q) /\ (p -> r)) -> (L |- p -> (q /\ r))

def composition [Im : Imp P] [Cj : Conj P] 
[K : Composition L Im Cj] {p q : P} := K.composition p q

-- DeMorgan's Law (1)
-- ~(p /\ q) |- ~p \/ ~q

class ConjDeMorgan (Cj : Conj P) (Dj : Disj P) (Nt : LNot P) :=
  conjDeMorgan : (p q : P) -> (L |- ~(p /\ q)) -> (L |- ~p \/ ~q)

def conjDeMorgan {L} [Cj : Conj P] [Dj : Disj P] [Nt : LNot P]
[K : ConjDeMorgan L Cj Dj Nt] {p q : P} := K.conjDeMorgan p q

-- DeMorgan's Law (2)
-- ~(p \/ q) |- ~p /\ ~q

class DisjDeMorgan (Cj : Conj P) (Dj : Disj P) (Nt : LNot P) :=
  disjDeMorgan : (p q : P) -> (L |- ~(p \/ q)) -> (L |- ~p /\ ~q)

def disjDeMorgan {L} [Cj : Conj P] [Dj : Disj P] [Nt : LNot P]
[K : DisjDeMorgan L Cj Dj Nt] {p q : P} := K.disjDeMorgan p q

-- Transposition
-- p -> q |- ~q -> ~p

class Transposition (Im : Imp P) (Nt : LNot P) :=
  transposition : (p q : P) -> (L |- p -> q) -> (L |- ~q -> ~p)

def transposition {L} [Im : Imp P] [Nt : LNot P]
[K : Transposition L Im Nt] {p q : P} := K.transposition p q

-- Material Implication
-- p -> q -|- ~p \/ q

class MatImpIntro (Im : Imp P) (Dj : Disj P) (Nt : LNot P) :=
  matImpIntro : (p q : P) -> (L |- ~p \/ q) -> (L |- p -> q)

def matImpIntro {L} [Im : Imp P] [Dj : Disj P] [Nt : LNot P]
[K : MatImpIntro L Im Dj Nt] {p q : P} := K.matImpIntro p q

class MatImpElim (Im : Imp P) (Dj : Disj P) (Nt : LNot P) :=
  matImpElim : (p q : P) -> (L |- p -> q) -> (L |- ~p \/ q)

def matImpElim {L} [Im : Imp P] [Dj : Disj P] [Nt : LNot P]
[K : MatImpElim L Im Dj Nt] {p q : P} := K.matImpElim p q

-- Material Equivalence
-- (p <-> q) -|- (p /\ q) \/ (~p /\ ~q)

class MatEqvIntro (Iff : LIff P) (Cj : Conj P) (Dj : Disj P) (Nt : LNot P) :=
  matEqvIntro : (p q : P) -> (L |- (p /\ q) \/ (~p /\ ~q)) -> (L |- p <-> q)

def matEqvIntro {L} [Iff : LIff P] [Cj : Conj P] [Dj : Disj P] [Nt : LNot P]
[K : MatEqvIntro L Iff Cj Dj Nt] {p q : P} := K.matEqvIntro p q

class MatEqvElim (Iff : LIff P) (Cj : Conj P) (Dj : Disj P) (Nt : LNot P) :=
  matEqvElim : (p q : P) -> (L |- p <-> q) -> (L |- (p /\ q) \/ (~p /\ ~q))

def matEqvElim {L} [Iff : LIff P] [Cj : Conj P] [Dj : Disj P] [Nt : LNot P]
[K : MatEqvElim L Iff Cj Dj Nt] {p q : P} := K.matEqvElim p q

-- Exportation
-- (p /\ q) -> r |- p -> (q -> r)

class Exprt (Im : Imp P) (Cj : Conj P) :=
  exprt : (p q r : P) -> (L |- (p /\ q) -> r) -> (L |- p -> (q -> r))

def exprt {L} [Im : Imp P] [Cj : Conj P]
[K : Exprt L Im Cj] {p q r : P} := K.exprt p q r

-- Importation
-- p -> (q -> r) |- (p /\ q) -> r

class Imprt (Im : Imp P) (Cj : Conj P) :=
  imprt : (p q r : P) -> (L |- p -> (q -> r)) -> (L |- (p /\ q) -> r)

def imprt {L} [Im : Imp P] [Cj : Conj P]
[K : Imprt L Im Cj] {p q : P} := K.imprt p q

-- Law of the Excluded Middle
-- |- p \/ ~p

class ExcludedMiddle (Dj : Disj P) (Nt : LNot P) :=
  em : (p : P) -> (L |- p \/ ~p)

def em {L} [Dj : Disj P] [Nt : LNot P]
[K : ExcludedMiddle L Dj Nt] {p : P} := K.em p

-- Law of Non-Contradiction
-- |- p \/ ~p

class NonContradiction (Cj : Conj P) (Nt : LNot P) :=
  nc : (p : P) -> (L |- ~(p /\ ~p))

def nc {L} [Cj : Conj P] [Nt : LNot P]
[K : NonContradiction L Cj Nt] {p : P} := K.nc p

end Gaea.Logic