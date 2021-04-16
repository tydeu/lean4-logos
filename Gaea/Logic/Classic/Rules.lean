import Gaea.Logic.Judgment
import Gaea.Logic.Prop.Rules
import Gaea.Logic.Rel.Rules

namespace Gaea.Logic

universe u
variable {P : Sort u}

-- Modus Ponens
-- (p -> q) /\ p |- q 

class ConjMp (L : Logic P) (imp : Binar P) (conj : Binar P) :=
  conjMp : (p q : P) -> (L |- (p -> q) /\ p) -> (L |- q) 

def conjMp {L : Logic p} {imp conj}
  [K : ConjMp L imp conj] {p q} := K.conjMp p q

instance iConjMpByUncurryMp
  {L : Logic P} {imp : Binar P} {conj : Binar P} 
  [CjU : Uncurry L conj] [Mp : ModusPonens L imp] 
  : ConjMp L imp conj := {conjMp := fun p q => uncurry mp}

-- Modus Tollens
-- (p -> q) /\ ~q |- ~p 

class ConjMt (L : Logic P) (imp : Binar P) (conj : Binar P) (lneg : Unar P) :=
  conjMt : (p q : P) -> (L |- (p -> q) /\ ~q) -> (L |- ~p) 

def conjMt {L : Logic P} {imp conj lneg}
  [K : ConjMt L imp conj lneg] {p q} := K.conjMt p q

instance iConjMtByUncurryMt {L : Logic P} 
  {imp : Binar P} {conj : Binar P} {lneg : Unar P}
  [CjU : Uncurry L conj] [Mt : ModusTollens L imp lneg] 
  : ConjMt L imp conj lneg := {conjMt := fun p q => uncurry mt}

-- Hypothetical Syllogism
-- (p -> q) /\ (q -> r) |- (p -> r) 

class HypoSyl (L : Logic P) (imp : Binar P) (conj : Binar P) :=
  hypoSyl : (p q r : P) -> (L |- (p -> q) /\ (q -> r)) -> (L |- p -> r) 

def hypoSyl {L : Logic P} {imp conj}
  [K : HypoSyl L imp conj] {p q r} := K.hypoSyl p q r

instance iHypoSylByUncurryTrans {L : Logic P} 
  {imp : Binar P} {conj : Binar P}
  [CjU : Uncurry L conj] [Itr : Trans L imp]
  : HypoSyl L imp conj := {hypoSyl := fun p q r => uncurry trans}

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

class CnstrDil (L : Logic P) (imp : Binar P) (conj : Binar P) (disj : Binar P) :=
  cnstrDil : (p q r s : P) -> 
    (L |- (p -> q) /\ (r -> s) /\ (p \/ r)) -> (L |- q \/ s) 

def cnstrDil {L : Logic P} {imp conj disj}
  [K : CnstrDil L imp conj disj] {p q r s} := K.cnstrDil p q r s

-- Destructive Dilemma
-- (p -> q) /\ (r -> s) /\ (~q \/ ~s) |- ~p \/ ~r 

class DestrDil (L : Logic P) 
  (imp : Binar P) (conj : Binar P) (disj : Binar P) (lneg : Unar P) :=
  destrDil : (p q r s : P) -> 
    (L |- (p -> q) /\ (r -> s) /\ (~q \/ ~s)) -> (L |- ~p \/ ~r) 

def destrDil {L : Logic P} {imp conj disj lneg}
  [K : DestrDil L imp conj disj lneg] {p q r s} := K.destrDil p q r s

-- Bidirectional Dilemma
-- (p -> q) /\ (r -> s) /\ (p \/ ~s) |- q \/ ~r 

class BidirDil (L : Logic P) 
  (imp : Binar P) (conj : Binar P) (disj : Binar P) (lneg : Unar P) :=
  bidirDil : (p q r s : P) -> 
    (L |- (p -> q) /\ (r -> s) /\ (p \/ ~s)) -> (L |- q \/ ~r) 

def bidirDil {L : Logic P} {imp conj disj lneg}
  [K : BidirDil L imp conj disj lneg] {p q r s} := K.bidirDil p q r s

-- Composition
-- (p -> q) /\ (p -> r) |- p -> (q /\ r)

class Composition (L : Logic P) (imp : Binar P) (conj : Binar P) :=
  composition : (p q r : P) -> (L |- (p -> q) /\ (p -> r)) -> (L |- p -> (q /\ r))

def composition {L : Logic P} {imp conj} 
  [K : Composition L imp conj] {p q} := K.composition p q

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

class Transposition (L : Logic P) (imp : Binar P) (lneg : Unar P) :=
  transposition : (p q : P) -> (L |- p -> q) -> (L |- ~q -> ~p)

def transposition {L : Logic P} [imp : Binar P] [lneg : Unar P]
[K : Transposition L imp lneg] {p q} := K.transposition p q

-- Material impplication
-- p -> q -|- ~p \/ q

class MatimppIntro (L : Logic P) (imp : Binar P) (disj : Binar P) (lneg : Unar P) :=
  matimppIntro : (p q : P) -> (L |- ~p \/ q) -> (L |- p -> q)

def matimppIntro {L : Logic P} {imp disj lneg}
  [K : MatimppIntro L imp disj lneg] {p q} := K.matimppIntro p q

class MatimppElim (L : Logic P) (imp : Binar P) (disj : Binar P) (lneg : Unar P) :=
  matimppElim : (p q : P) -> (L |- p -> q) -> (L |- ~p \/ q)

def matimppElim {L : Logic P} {imp disj lneg}
  [K : MatimppElim L imp disj lneg] {p q} := K.matimppElim p q

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

class Exprt (L : Logic P) (imp : Binar P) (conj : Binar P) :=
  exprt : (p q r : P) -> (L |- (p /\ q) -> r) -> (L |- p -> (q -> r))

def exprt {L : Logic P} {imp conj}
  [K : Exprt L imp conj] {p q r} := K.exprt p q r

-- impportation
-- p -> (q -> r) |- (p /\ q) -> r

class impprt (L : Logic P) (imp : Binar P) (conj : Binar P) :=
  imprt : (p q r : P) -> (L |- p -> (q -> r)) -> (L |- (p /\ q) -> r)

def imprt {L : Logic P} {imp conj}
  [K : impprt L imp conj] {p q} := K.imprt p q

-- Law of the Excluded Middle
-- |- p \/ ~p

def em {L : Logic P} {disj : Binar P} {lneg : Unar P} {p : P}
  [K : Postulate L (p \/ ~p)] := K.postulate

-- Law of Non-Contradiction
-- |- p \/ ~p

def nc {L : Logic P} {conj : Binar P} {lneg : Unar P} {p : P}
  [K : Postulate L ~(p /\ ~p)] := K.postulate

end Gaea.Logic