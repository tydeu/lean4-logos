import Gaea.Logic.Judgment
import Gaea.Logic.Rel.Rules
import Gaea.Logic.Fun.Rules
import Gaea.Logic.Unit.Rules
import Gaea.Logic.Dual.Rules

namespace Gaea.Logic

universe u
variable {P : Sort u}

-- Modus Ponens
-- (p -> q) /\ p |- q 

class ConjMp (L : Logic P) (larr : Binar P) (conj : Binar P) :=
  conjMp : (p q : P) -> (L |- (p -> q) /\ p) -> (L |- q) 

def conjMp {L : Logic p} {larr conj}
  [K : ConjMp L larr conj] {p q} := K.conjMp p q

instance iConjMpByUncurryMp
  {L : Logic P} {larr : Binar P} {conj : Binar P} 
  [CjU : Uncurry L conj] [Mp : ModusPonens L larr] 
  : ConjMp L larr conj := {conjMp := fun p q => uncurry mp}

-- Modus Tollens
-- (p -> q) /\ ~q |- ~p 

class ConjMt (L : Logic P) (larr : Binar P) (conj : Binar P) (lneg : Unar P) :=
  conjMt : (p q : P) -> (L |- (p -> q) /\ ~q) -> (L |- ~p) 

def conjMt {L : Logic P} {larr conj lneg}
  [K : ConjMt L larr conj lneg] {p q} := K.conjMt p q

instance iConjMtByUncurryMt {L : Logic P} 
  {larr : Binar P} {conj : Binar P} {lneg : Unar P}
  [CjU : Uncurry L conj] [Mt : ModusTollens L larr lneg] 
  : ConjMt L larr conj lneg := {conjMt := fun p q => uncurry mt}

-- Hypothetical Syllogism
-- (p -> q) /\ (q -> r) |- (p -> r) 

class HypoSyl (L : Logic P) (larr : Binar P) (conj : Binar P) :=
  hypoSyl : (p q r : P) -> (L |- (p -> q) /\ (q -> r)) -> (L |- p -> r) 

def hypoSyl {L : Logic P} {larr conj}
  [K : HypoSyl L larr conj] {p q r} := K.hypoSyl p q r

instance iHypoSylByUncurryTrans {L : Logic P} 
  {larr : Binar P} {conj : Binar P}
  [CjU : Uncurry L conj] [Itr : Trans L larr]
  : HypoSyl L larr conj := {hypoSyl := fun p q r => uncurry trans}

-- Disjunctive Syllogism
-- (p \/ q) /\ ~p |- q 

class DisjSyl (L : Logic P) (conj : Binar P) (disj : Binar P) (lneg : Unar P) :=
  disjSyl : (p q : P) -> (L |- (p \/ q) /\ ~p) -> (L |- q) 

def disjSyl {L : Logic P} {conj disj lneg}
  [K : DisjSyl L conj disj lneg] {p q} := K.disjSyl p q

instance iDisjSylByUncurryMtp {L : Logic P} 
  {conj : Binar P} {disj : Binar P} {lneg : Unar P} 
  [CjU : Uncurry L conj] [Mtp : ModusTollendoPonens L disj lneg]
  : DisjSyl L conj disj lneg :=  {disjSyl := fun p q => uncurry mtp}

-- Constructive Dilemma
-- (p -> q) /\ (r -> s) /\ (p \/ r) |- q \/ s 

class CnstrDil (L : Logic P) (larr : Binar P) (conj : Binar P) (disj : Binar P) :=
  cnstrDil : (p q r s : P) -> 
    (L |- (p -> q) /\ (r -> s) /\ (p \/ r)) -> (L |- q \/ s) 

def cnstrDil {L : Logic P} {larr conj disj}
  [K : CnstrDil L larr conj disj] {p q r s} := K.cnstrDil p q r s

-- Destructive Dilemma
-- (p -> q) /\ (r -> s) /\ (~q \/ ~s) |- ~p \/ ~r 

class DestrDil (L : Logic P) 
  (larr : Binar P) (conj : Binar P) (disj : Binar P) (lneg : Unar P) :=
  destrDil : (p q r s : P) -> 
    (L |- (p -> q) /\ (r -> s) /\ (~q \/ ~s)) -> (L |- ~p \/ ~r) 

def destrDil {L : Logic P} {larr conj disj lneg}
  [K : DestrDil L larr conj disj lneg] {p q r s} := K.destrDil p q r s

-- Bidirectional Dilemma
-- (p -> q) /\ (r -> s) /\ (p \/ ~s) |- q \/ ~r 

class BidirDil (L : Logic P) 
  (larr : Binar P) (conj : Binar P) (disj : Binar P) (lneg : Unar P) :=
  bidirDil : (p q r s : P) -> 
    (L |- (p -> q) /\ (r -> s) /\ (p \/ ~s)) -> (L |- q \/ ~r) 

def bidirDil {L : Logic P} {larr conj disj lneg}
  [K : BidirDil L larr conj disj lneg] {p q r s} := K.bidirDil p q r s

-- Composition
-- (p -> q) /\ (p -> r) |- p -> (q /\ r)

class Composition (L : Logic P) (larr : Binar P) (conj : Binar P) :=
  composition : (p q r : P) -> (L |- (p -> q) /\ (p -> r)) -> (L |- p -> (q /\ r))

def composition {L : Logic P} {larr conj} 
  [K : Composition L larr conj] {p q} := K.composition p q

-- DeMorgan's Law (1)
-- ~(p /\ q) |- ~p \/ ~q

class ConjDeMorgan (L : Logic P) (conj : Binar P) (disj : Binar P) (lneg : Unar P) :=
  conjDeMorgan : (p q : P) -> (L |- ~(p /\ q)) -> (L |- ~p \/ ~q)

def conjDeMorgan {L : Logic P} {conj disj lneg}
  [K : ConjDeMorgan L conj disj lneg] {p q} := K.conjDeMorgan p q

-- DeMorgan's Law (2)
-- ~(p \/ q) |- ~p /\ ~q

class DisjDeMorgan (L : Logic P) (conj : Binar P) (disj : Binar P) (lneg : Unar P) :=
  disjDeMorgan : (p q : P) -> (L |- ~(p \/ q)) -> (L |- ~p /\ ~q)

def disjDeMorgan {L : Logic P} {conj disj lneg}
  [K : DisjDeMorgan L conj disj lneg] {p q} := K.disjDeMorgan p q

-- Transposition
-- p -> q |- ~q -> ~p

class Transposition (L : Logic P) (larr : Binar P) (lneg : Unar P) :=
  transposition : (p q : P) -> (L |- p -> q) -> (L |- ~q -> ~p)

def transposition {L : Logic P} [larr : Binar P] [lneg : Unar P]
[K : Transposition L larr lneg] {p q} := K.transposition p q

-- Material Implication
-- p -> q -|- ~p \/ q

class MatImpIntro (L : Logic P) (larr : Binar P) (disj : Binar P) (lneg : Unar P) :=
  matImpIntro : (p q : P) -> (L |- ~p \/ q) -> (L |- p -> q)

def matImpIntro {L : Logic P} {larr disj lneg}
  [K : MatImpIntro L larr disj lneg] {p q} := K.matImpIntro p q

class MatImpElim (L : Logic P) (larr : Binar P) (disj : Binar P) (lneg : Unar P) :=
  matImpElim : (p q : P) -> (L |- p -> q) -> (L |- ~p \/ q)

def matImpElim {L : Logic P} {larr disj lneg}
  [K : MatImpElim L larr disj lneg] {p q} := K.matImpElim p q

-- Material Equivalence
-- (p <-> q) -|- (p /\ q) \/ (~p /\ ~q)

class MatEqvIntro (L : Logic P) 
  (iff : Binar P) (conj : Binar P) (disj : Binar P) (lneg : Unar P) :=
  matEqvIntro : (p q : P) -> (L |- (p /\ q) \/ (~p /\ ~q)) -> (L |- p <-> q)

def matEqvIntro {L : Logic P} {iff conj disj lneg}
  [K : MatEqvIntro L iff conj disj lneg] {p q} := K.matEqvIntro p q

class MatEqvElim (L : Logic P) 
  (iff : Binar P) (conj : Binar P) (disj : Binar P) (lneg : Unar P) :=
  matEqvElim : (p q : P) -> (L |- p <-> q) -> (L |- (p /\ q) \/ (~p /\ ~q))

def matEqvElim {L : Logic P} {iff conj disj lneg}
  [K : MatEqvElim L iff conj disj lneg] {p q} := K.matEqvElim p q

-- Exportation
-- (p /\ q) -> r |- p -> (q -> r)

class Exprt (L : Logic P) (larr : Binar P) (conj : Binar P) :=
  exprt : (p q r : P) -> (L |- (p /\ q) -> r) -> (L |- p -> (q -> r))

def exprt {L : Logic P} {larr conj}
  [K : Exprt L larr conj] {p q r} := K.exprt p q r

-- Importation
-- p -> (q -> r) |- (p /\ q) -> r

class Imprt (L : Logic P) (larr : Binar P) (conj : Binar P) :=
  imprt : (p q r : P) -> (L |- p -> (q -> r)) -> (L |- (p /\ q) -> r)

def imprt {L : Logic P} {larr conj}
  [K : Imprt L larr conj] {p q} := K.imprt p q

-- Law of the Excluded Middle
-- |- p \/ ~p

def em {L : Logic P} {disj : Binar P} {lneg : Unar P} {p : P}
  [K : Postulate L (p \/ ~p)] := K.postulate

-- Law of Non-Contradiction
-- |- p \/ ~p

def nc {L : Logic P} {conj : Binar P} {lneg : Unar P} {p : P}
  [K : Postulate L ~(p /\ ~p)] := K.postulate

end Gaea.Logic