import Gaea.Function
import Gaea.Logic.Judgment
import Gaea.Logic.Prop.Syntax
import Gaea.Logic.Prop.Notation

universes u v w
variable {P : Sort u} {T : Sort v}

namespace Gaea.Logic

--------------------------------------------------------------------------------
-- Postulate
--------------------------------------------------------------------------------

class Postulate (L : Logic P) (p : P) := 
  postulate : L |- p 

abbrev postulate {L : Logic P} {p}
  [K : Postulate L p] := K.postulate

--------------------------------------------------------------------------------
-- Implication (if)
--------------------------------------------------------------------------------

-- Conditional Proof
-- ((|- p) -> (|- q)) -> (|- p -> q) 

class ByImplication (L : Logic P) (imp : Binar P) := 
  byImplication : (p q : P) -> ((L |- p) -> (L |- q)) -> (L |- p -> q) 

abbrev byImplication {L : Logic P} {imp} 
  [K : ByImplication L imp] {p q} := K.byImplication p q

--------------------------------------------------------------------------------
-- Contraposition
--------------------------------------------------------------------------------

-- Proof by Contraposition
-- ((|- ~q) -> (|- ~p)) -> (|- p -> q)

class ByContraposition (L : Logic P) (imp : Binar P) (lnot : Unar P) :=
  byContraposition : (p q : P) -> ((L |- ~q) -> (L |- ~p)) -> (L |- p -> q) 

abbrev byContraposition {L : Logic P} {imp lnot}
  [K : ByContraposition L imp lnot] {p q} := K.byContraposition p q

--------------------------------------------------------------------------------
-- Biconditional (iff)
--------------------------------------------------------------------------------

-- Biconditional Introduction
-- ((|- p) -> (|- q)) -> ((|- q) -> (|- p)) -> (|- p <-> q)

class Bicondition (L : Logic P) (iff : Binar P) := 
  bicondition : (p q : P) -> 
    ((L |- p) -> (L |- q)) -> ((L |- q) -> (L |- p)) -> (L |- p <-> q)

abbrev bicondition {L : Logic P} {iff}
  [K : Bicondition L iff] {p q} := K.bicondition p q

--------------------------------------------------------------------------------
-- Modus Ponens
--------------------------------------------------------------------------------

-- (|- p <-> q) -> (|- p) -> (|- q)

class ModusPonens (L : Logic P) (iff : Binar P) := 
  mp : (p q : P) -> (L |- p <-> q) -> (L |- p) -> (L |- q)

abbrev mp {L : Logic P} {iff} 
  [K : ModusPonens L iff] {p q} := K.mp p q

-- (|- p <-> q) -> (|- q) -> (|- p)

class ModusPonensRev (L : Logic P) (iff : Binar P) := 
  mpr : (p q : P) -> (L |- p <-> q) -> (L |- q) -> (L |- p)

abbrev mpr {L : Logic P} {iff} 
  [K : ModusPonensRev L iff] {p q} := K.mpr p q

--------------------------------------------------------------------------------
-- Modus Tollens
--------------------------------------------------------------------------------

-- (|- p <-> q) -> (|- ~q) -> (|- ~p) 

class ModusTollens (L : Logic P) (iff : Binar P) (lnot : Unar P) :=
  mt : (p q : P) -> (L |- p <-> q) -> (L |- ~q) -> (L |- ~p)

abbrev mt {L : Logic P} {iff lnot} 
  [K : ModusTollens L iff lnot] {p q} := K.mt p q

-- (|- p <-> q) -> (|- ~p) -> (|- ~q) 

class ModusTollensRev (L : Logic P) (iff : Binar P) (lnot : Unar P) :=
  mtr : (p q : P) -> (L |- p <-> q) -> (L |- ~p) -> (L |- ~q) 

abbrev mtr {L : Logic P} {iff lnot} 
  [K : ModusTollensRev L iff lnot] {p q} := K.mtr p q

--------------------------------------------------------------------------------
-- Conjunction
--------------------------------------------------------------------------------

-- p, q |- p /\ q

class ConjIntro (L : Logic P) (Cj : Conj P) := 
  conjIntro : (p q : P) -> (L |- p) -> (L |- q) -> (L |- p /\ q) 

abbrev conjIntro {L : Logic P} [Cj : Conj P] 
  [K : ConjIntro L Cj] {p q} := K.conjIntro p q

-- p /\ q -> p

class ConjLeft (L : Logic P) (Cj : Conj P) := 
  conjLeft : (p q : P) -> (L |- p /\ q) -> (L |- p)

abbrev conjLeft {L : Logic P} [Cj : Conj P] 
  [K : ConjLeft L Cj] {p q} := K.conjLeft p q

-- p /\ q -> q

class ConjRight (L : Logic P) (Cj : Conj P) := 
  conjRight : (p q : P) -> (L |- p /\ q) -> (L |- q)

abbrev conjRight {L : Logic P} [Cj : Conj P] 
  [K : ConjRight L Cj] {p q} := K.conjRight p q

-- p -> p /\ p

class ConjTaut (L : Logic P) (Cj : Conj P)  :=
  conjTaut : (p : P) -> (L |- p) -> (L |- p /\ p)

abbrev conjTaut {L : Logic P} [Cj : Conj P] 
  [K : ConjTaut L Cj] {p} := K.conjTaut p

instance iConjTautOfIntro {L : Logic P} [Cj : Conj P]
  [K : ConjIntro L Cj] : ConjTaut L Cj := 
  {conjTaut := fun p Lp => K.conjIntro p p Lp Lp}

-- p /\ p -> p

class ConjSimp (L : Logic P) (Cj : Conj P)  :=
  conjSimp : (p : P) -> (L |- p /\ p) -> (L |- p)

abbrev conjSimp {L : Logic P} [Cj : Conj P] 
  [K : ConjSimp L Cj] {p} := K.conjSimp p

instance iConjSimpOfLeft {L : Logic P} [Cj : Conj P]
  [K : ConjLeft L Cj] : ConjSimp L Cj := 
  {conjSimp := fun p LpCq => K.conjLeft p p LpCq}

instance iConjSimpOfRight {L : Logic P} [Cj : Conj P]
  [K : ConjRight L Cj] : ConjSimp L Cj := 
  {conjSimp := fun p LpCq => K.conjRight p p LpCq}

-- (p /\ q -> a) -> (p -> q -> a)

class ConjCurry (L : Logic P) (Cj : Conj P) :=
  conjCurry : (r : Sort w) -> (p q : P) -> 
    ((L |- p /\ q) -> r) -> ((L |- p) -> (L |- q) -> r)

abbrev conjCurry {L : Logic P} [Cj : Conj P] 
  [K : ConjCurry L Cj] {r p q} := K.conjCurry r p q

instance iConjCurryOfIntro {L : Logic P} [Cj : Conj P]
  [CjI : ConjIntro L Cj] : ConjCurry L Cj := 
  {conjCurry := fun a p q fpCq Lp Lq  => fpCq (conjIntro Lp Lq)}

-- (p -> q -> a) -> (p /\ q -> a)

class ConjUncurry (L : Logic P) (Cj : Conj P) :=
  conjUncurry : (r : Sort w) -> (p q : P) -> 
    ((L |- p) -> (L |- q) -> r) -> ((L |- p /\ q) -> r)

abbrev conjUncurry {L : Logic P} [Cj : Conj P] 
  [K : ConjUncurry L Cj] {r p q} := K.conjUncurry r p q

instance iConjUncurryOfLeftRight {L : Logic P} [Cj : Conj P]
  [CjL : ConjLeft L Cj] [CjR : ConjRight L Cj] : ConjUncurry L Cj := 
  {conjUncurry := fun a p q fpq LpCq => fpq (conjLeft LpCq) (conjRight LpCq)}

-- Prod p q -> p /\ q 

class ConjOfProd (L : Logic P) (Cj : Conj P) := 
  conjOfProd : (p q : P) -> Prod (L |- p) (L |- q) -> (L |- p /\ q)

abbrev conjOfProd {L : Logic P} [Cj : Conj P] 
  [K : ConjOfProd L Cj] {p q} := K.conjOfProd p q

instance iConjIntroOfProd {L : Logic P} [Cj : Conj P] 
  [K : ConjOfProd L Cj] : ConjIntro L Cj := 
  {conjIntro := fun p q Lp Lq => K.conjOfProd p q (Prod.mk Lp Lq)}

instance iConjOfProdOfIntro {L : Logic P} [Cj : Conj P] 
  [K : ConjIntro L Cj] : ConjOfProd L Cj := 
  {conjOfProd := fun p q Ppq => K.conjIntro p q Ppq.fst Ppq.snd}

-- PProd p q -> p /\ q 

class ConjOfPProd (L : Logic P) (Cj : Conj P) := 
  conjOfPProd : (p q : P) -> PProd (L |- p) (L |- q) -> (L |- p /\ q)

abbrev conjOfPProd {L : Logic P} [Cj : Conj P] 
  [K : ConjOfPProd L Cj] {p q} := K.conjOfPProd p q

instance iConjIntroOfPProd {L : Logic P} [Cj : Conj P] 
  [K : ConjOfPProd L Cj] : ConjIntro L Cj := 
  {conjIntro := fun p q Lp Lq => K.conjOfPProd p q (PProd.mk Lp Lq)}

instance iConjOfPProdOfIntro {L : Logic P} [Cj : Conj P] 
  [K : ConjIntro L Cj] : ConjOfPProd L Cj := 
  {conjOfPProd := fun p q Ppq => K.conjIntro p q Ppq.fst Ppq.snd}

instance iConjOfProdOfPProd {L : Logic P} [Cj : Conj P] 
  [K : ConjOfPProd L Cj] : ConjOfProd L Cj := 
  {conjOfProd := fun p q Ppq => K.conjOfPProd p q (PProd.mk (Ppq.fst) (Ppq.snd))}

-- And p q -> p /\ q 

class ConjOfAnd (L : Logic P) (Cj : Conj P) := 
  conjOfAnd : (p q : P) -> (L |- p) /\ (L |- q) -> (L |- p /\ q)

abbrev conjOfAnd {L : Logic P} [Cj : Conj P] 
  [K : ConjOfAnd L Cj] {p q} := K.conjOfAnd p q

instance iConjIntroOfAnd {L : Logic P} [Cj : Conj P] 
  [K : ConjOfAnd L Cj] : ConjIntro L Cj := 
  {conjIntro := fun p q Lp Lq => K.conjOfAnd p q (And.intro Lp Lq)}

instance iConjOfAndOfIntro {L : Logic P} [Cj : Conj P] 
  [K : ConjIntro L Cj] : ConjOfAnd L Cj := 
  {conjOfAnd := fun p q Apq => K.conjIntro p q Apq.left Apq.right}

-- p /\ q -> Prod p q

class ConjAsProd (L : Logic P) (Cj : Conj P) := 
  conjAsProd : (p q : P) -> (L |- p /\ q) -> Prod (L |- p) (L |- q)

abbrev conjAsProd {L : Logic P} [Cj : Conj P] 
  [K : ConjAsProd L Cj] {p q} := K.conjAsProd p q

instance iConjAsProdOfLeftRight {L : Logic P} [Cj : Conj P]
  [CjL : ConjLeft L Cj] [CjR : ConjRight L Cj] : ConjAsProd L Cj := 
  {conjAsProd := fun p q LpCq => Prod.mk (conjLeft LpCq) (conjRight LpCq)}

instance iConjLeftOfAsProd {L : Logic P} [Cj : Conj P]
  [K : ConjAsProd L Cj] : ConjLeft L Cj := 
  {conjLeft := fun p q LpCq => Prod.fst (K.conjAsProd p q LpCq)}

instance iConjRightOfAsProd {L : Logic P} [Cj : Conj P]
  [K : ConjAsProd L Cj] : ConjRight L Cj := 
  {conjRight := fun p q LpCq => Prod.snd (K.conjAsProd p q LpCq)}

-- p /\ q -> PProd p q

class ConjAsPProd (L : Logic P) (Cj : Conj P) := 
  conjAsPProd : (p q : P) -> (L |- p /\ q) -> PProd (L |- p) (L |- q)

abbrev conjAsPProd {L : Logic P} [Cj : Conj P] 
  [K : ConjAsPProd L Cj] {p q} := K.conjAsPProd p q

instance iConjAsPProdOfLeftRight {L : Logic P} [Cj : Conj P]
  [CjL : ConjLeft L Cj] [CjR : ConjRight L Cj] : ConjAsPProd L Cj := 
  {conjAsPProd := fun p q LpCq => PProd.mk (conjLeft LpCq) (conjRight LpCq)}

instance iConjLeftOfAsPProd {L : Logic P} [Cj : Conj P]
  [K : ConjAsPProd L Cj] : ConjLeft L Cj := 
  {conjLeft := fun p q LpCq => PProd.fst (K.conjAsPProd p q LpCq)}

instance iConjRightOfAsPProd {L : Logic P} [Cj : Conj P]
  [K : ConjAsPProd L Cj] : ConjRight L Cj := 
  {conjRight := fun p q LpCq => PProd.snd (K.conjAsPProd p q LpCq)}

instance iConjAsProdOfPProd {L : Logic P} [Cj : Conj P]
  [K : ConjAsPProd L Cj] : ConjAsProd L Cj := 
  {conjAsProd := fun p q LpCq => Prod.mk (conjLeft LpCq) (conjRight LpCq)}

-- p /\ q -> And p q

class ConjAsAnd (L : Logic P) (Cj : Conj P) := 
  conjAsAnd : (p q : P) -> (L |- p /\ q) -> (L |- p) /\ (L |- q)

abbrev conjAsAnd {L : Logic P} [Cj : Conj P] 
  [K : ConjAsAnd L Cj] {p q} := K.conjAsAnd p q

instance iConjAsAndOfLeftRight {L : Logic P} [Cj : Conj P]
  [CjL : ConjLeft L Cj] [CjR : ConjRight L Cj] : ConjAsAnd L Cj := 
  {conjAsAnd := fun p q LpCq => And.intro (conjLeft LpCq) (conjRight LpCq)}

instance iConjLeftOfAsAnd {L : Logic P} [Cj : Conj P]
  [K : ConjAsAnd L Cj] : ConjLeft L Cj := 
  {conjLeft := fun p q LpCq => And.left (K.conjAsAnd p q LpCq)}

instance iConjRightOfAsAnd {L : Logic P} [Cj : Conj P]
  [K : ConjAsAnd L Cj] : ConjRight L Cj := 
  {conjRight := fun p q LpCq => And.right (K.conjAsAnd p q LpCq)}

--------------------------------------------------------------------------------
-- Disjunction
--------------------------------------------------------------------------------

-- p -> p \/ q

class DisjIntroLeft (L : Logic P) (Dj : Disj P)  := 
  disjIntroLeft : (p q : P) -> (L |- p) -> (L |- p \/ q) 

abbrev disjIntroLeft {L : Logic P} [Dj : Disj P] 
  [K : DisjIntroLeft L Dj] {p q} := K.disjIntroLeft p q

-- q -> p \/ q

class DisjIntroRight (L : Logic P) (Dj : Disj P)  := 
  disjIntroRight : (p q : P) -> (L |- q) -> (L |- p \/ q) 

abbrev disjIntroRight {L : Logic P} [Dj : Disj P] 
  [K : DisjIntroRight L Dj] {p q} := K.disjIntroRight p q

-- p \/ q -> (p -> r) -> (q -> r) -> r

class DisjElim (L : Logic P) (Dj : Disj P) := 
  disjElim : (r : Sort w) -> (p q : P) -> 
    (L |- p \/ q) -> ((L |- p) -> r) -> ((L |- q) -> r) -> r

abbrev disjElim {L : Logic P} [Dj : Disj P]
  [K : DisjElim L Dj] {r p q} := K.disjElim r p q

-- p -> p \/ p

class DisjTaut (L : Logic P) (Dj : Disj P) :=
  disjTaut : (p : P) -> (L |- p) -> (L |- p \/ p)

abbrev disjTaut {L : Logic P} [Dj : Disj P] 
  [K : DisjTaut L Dj] {p} := K.disjTaut p

instance iDisjTautOfIntroLeft {L : Logic P} [Dj : Disj P]
  [K : DisjIntroLeft L Dj] : DisjTaut L Dj := 
  {disjTaut := fun p Lp => K.disjIntroLeft p p Lp}

instance iDisjTautOfIntroRight {L : Logic P} [Dj : Disj P]
  [K : DisjIntroRight L Dj] : DisjTaut L Dj := 
  {disjTaut := fun p Lp => K.disjIntroRight p p Lp}

-- p \/ p -> p

class DisjSimp (L : Logic P) (Dj : Disj P) :=
  disjSimp : (p : P) -> (L |- p \/ p) -> (L |- p)

abbrev disjSimp {L : Logic P} [Dj : Disj P] 
  [K : DisjSimp L Dj] {p} := K.disjSimp p

instance iDisjSimpOfElim {L : Logic P} [Dj : Disj P]
  [K : DisjElim L Dj] : DisjSimp L Dj := 
  {disjSimp := fun p LpDp => K.disjElim _ p p LpDp id id}

-- p \/ q -> ~p -> q

class DisjElimLeft (L : Logic P) (Dj : Disj P) (lnot : Unar P) := 
  disjElimLeft : (p q : P) -> (L |- p \/ q) -> (L |- ~p) -> (L |- q)

abbrev disjElimLeft {L : Logic P} [Dj : Disj P] {lnot : Unar P} 
  [K : DisjElimLeft L Dj lnot] {p q} := K.disjElimLeft p q

-- p \/ q -> ~q -> p

class DisjElimRight (L : Logic P) (Dj : Disj P) (lnot : Unar P) := 
  disjElimRight : (p q : P) -> (L |- p \/ q) -> (L |- ~q) -> (L |- p)

abbrev disjElimRight {L : Logic P} [Dj : Disj P] {lnot : Unar P} 
  [K : DisjElimRight L Dj lnot] {p q} := K.disjElimRight p q

-- Sum p q -> p \/ q 

class DisjOfSum (L : Logic P) (Dj : Disj P) := 
  disjOfSum : (p q : P) -> Sum (L |- p) (L |- q) -> (L |- p \/ q)

abbrev disjOfSum {L : Logic P} [Dj : Disj P] 
  [K : DisjOfSum L Dj] {p q} := K.disjOfSum p q

instance iDisjOfSumOfIntro {L : Logic P} [Dj : Disj P] 
  [DiL : DisjIntroLeft L Dj] [DiR : DisjIntroRight L Dj] : DisjOfSum L Dj := 
  {disjOfSum := fun p q Spq => match Spq with 
    | Sum.inl Lp => disjIntroLeft Lp | Sum.inr Lq => disjIntroRight Lq}

instance iDisjIntroLeftOfSum {L : Logic P} [Dj : Disj P] 
  [K : DisjOfSum L Dj] : DisjIntroLeft L Dj := 
  {disjIntroLeft := fun p q Lp => K.disjOfSum p q (Sum.inl Lp)}

instance iDisjIntroRightOfSum {L : Logic P} [Dj : Disj P] 
  [K : DisjOfSum L Dj] : DisjIntroRight L Dj := 
  {disjIntroRight := fun p q Lq => K.disjOfSum p q (Sum.inr Lq)}

-- PSum p q -> p \/ q  

class DisjOfPSum (L : Logic P) (Dj : Disj P) := 
  disjOfPSum : (p q : P) -> PSum (L |- p) (L |- q) -> (L |- p \/ q)

abbrev disjOfPSum {L : Logic P} [Dj : Disj P] 
  [K : DisjOfPSum L Dj] {p q} := K.disjOfPSum p q

instance iDisjOfPSumOfIntro {L : Logic P} [Dj : Disj P] 
  [DiL : DisjIntroLeft L Dj] [DiR : DisjIntroRight L Dj] : DisjOfPSum L Dj := 
  {disjOfPSum := fun p q Spq => match Spq with 
    | PSum.inl Lp => disjIntroLeft Lp | PSum.inr Lq => disjIntroRight Lq}

instance iDisjIntroLeftOfPSum {L : Logic P} [Dj : Disj P] 
  [K : DisjOfPSum L Dj] : DisjIntroLeft L Dj := 
  {disjIntroLeft := fun p q Lp => K.disjOfPSum p q (PSum.inl Lp)}

instance iDisjIntroRightOfPSum {L : Logic P} [Dj : Disj P] 
  [K : DisjOfPSum L Dj] : DisjIntroRight L Dj := 
  {disjIntroRight := fun p q Lq => K.disjOfPSum p q (PSum.inr Lq)}

-- Or p q -> p \/ q 

class DisjOfOr (L : Logic P) (Dj : Disj P) := 
  disjOfOr : (p q : P) -> (L |- p) \/ (L |- q) -> (L |- p \/ q)

abbrev disjOfOr {L : Logic P} [Dj : Disj P] 
  [K : DisjOfOr L Dj] {p q} := K.disjOfOr p q

instance iDisjOfOrOfIntro {L : Logic P} [Dj : Disj P] 
  [DiL : DisjIntroLeft L Dj] [DiR : DisjIntroRight L Dj] : DisjOfOr L Dj := 
  {disjOfOr := fun p q Spq => match Spq with 
    | Or.inl Lp => disjIntroLeft Lp | Or.inr Lq => disjIntroRight Lq}

instance iDisjIntroLeftOfOr {L : Logic P} [Dj : Disj P] 
  [K : DisjOfOr L Dj] : DisjIntroLeft L Dj := 
  {disjIntroLeft := fun p q Lp => K.disjOfOr p q (Or.inl Lp)}

instance iDisjIntroRightOfOr {L : Logic P} [Dj : Disj P] 
  [K : DisjOfOr L Dj] : DisjIntroRight L Dj := 
  {disjIntroRight := fun p q Lq => K.disjOfOr p q (Or.inr Lq)}

-- p \/ q -> Sum p q 

class DisjAsSum (L : Logic P) (Dj : Disj P) := 
  disjAsSum : (p q : P) -> (L |- p \/ q) -> Sum (L |- p) (L |- q)

abbrev disjAsSum {L : Logic P} [Dj : Disj P] 
  [K : DisjAsSum L Dj] {p q} := K.disjAsSum p q

instance iDisjAsSumOfElim {L : Logic P} [Dj : Disj P] 
  [K : DisjElim L Dj] : DisjAsSum L Dj := 
  {disjAsSum := fun p q LpDq => K.disjElim _ p q LpDq Sum.inl Sum.inr}

instance iDisjElimOfAsSum {L : Logic P} [Dj : Disj P] 
  [K : DisjAsSum L Dj] : DisjElim L Dj := 
  {disjElim := fun a p q LpDq fpa fqa => match K.disjAsSum p q LpDq with
    | Sum.inl Lp => fpa Lp | Sum.inr Lq => fqa Lq}

-- p \/ q -> PSum p q 

class DisjAsPSum (L : Logic P) (Dj : Disj P) := 
  disjAsPSum : (p q : P) -> (L |- p \/ q) -> PSum (L |- p) (L |- q)

abbrev disjAsPSum {L : Logic P} [Dj : Disj P] 
  [K : DisjAsPSum L Dj] {p q} := K.disjAsPSum p q

instance iDisjAsPSumOfElim {L : Logic P} [Dj : Disj P] 
  [K : DisjElim L Dj] : DisjAsPSum L Dj := 
  {disjAsPSum := fun p q LpDq => K.disjElim _ p q LpDq PSum.inl PSum.inr}

instance iDisjElimOfAsPSum {L : Logic P} [Dj : Disj P] 
  [K : DisjAsPSum L Dj] : DisjElim L Dj := 
  {disjElim := fun a p q LpDq fpa fqa => match K.disjAsPSum p q LpDq with
    | PSum.inl Lp => fpa Lp | PSum.inr Lq => fqa Lq}

-- p \/ q -> Or p q 

class DisjAsOr (L : Logic P) (Dj : Disj P) := 
  disjAsOr : (p q : P) -> (L |- p \/ q) -> (L |- p) \/ (L |- q)

abbrev disjAsOr {L : Logic P} [Dj : Disj P] 
  [K : DisjAsOr L Dj] {p q} := K.disjAsOr p q

instance iDisjAsOrOfElim {L : Logic P} [Dj : Disj P] 
  [K : DisjElim L Dj] : DisjAsOr L Dj := 
  {disjAsOr := fun p q LpDq => K.disjElim _ p q LpDq Or.inl Or.inr}

instance iDisjElimOfAsOr {L : Logic P} [Dj : Disj P] 
  [K : DisjAsOr L Dj] : DisjElim L Dj := 
  {disjElim := fun (a : Prop) p q LpDq fpa fqa => match K.disjAsOr p q LpDq with
    | Or.inl Lp => fpa Lp | Or.inr Lq => fqa Lq}

--------------------------------------------------------------------------------
-- Not
--------------------------------------------------------------------------------

class NotIntro (L : Logic P) (lnot : Unar P) := 
  notIntro : (p : P) -> ((L |- p) -> False) -> (L |- ~p) 

abbrev notIntro {L : Logic P} {lnot}
  [K : NotIntro L lnot] {p} := K.notIntro p

class NotElim (L : Logic P) (lnot : Unar P) := 
  notElim : (p : P) -> (L |- lnot p) -> (L |- p) -> False

abbrev notElim {L : Logic P} {lnot} 
  [K : NotElim L lnot] {p} := K.notElim p

--------------------------------------------------------------------------------
-- Double Negation
--------------------------------------------------------------------------------

class DblNegIntro (L : Logic P) (lnot : Unar P) :=
  dblNegIntro : (p : P) -> (L |- p) -> (L |- ~~p)

abbrev dblNegIntro {L : Logic P} {lnot}
  [K : DblNegIntro L lnot] {p} := K.dblNegIntro p

class DblNegElim (L : Logic P) (lnot : Unar P) :=
  dblNegElim : (p : P) -> (L |- ~~p) -> (L |- p)

abbrev dblNegElim {L : Logic P} {lnot}
  [K : DblNegElim L lnot] {p} := K.dblNegElim p

--------------------------------------------------------------------------------
-- Contradiction
--------------------------------------------------------------------------------

def Contradiction (L : Logic P) (lnot : Unar P) :=
  PSigma fun (p : P) => PProd (L |- p) (L |- lnot p)

def contradiction {L : Logic P} {lnot}
  {p} (Lp : L |- p) (LNp : L |- lnot p) : Contradiction L lnot := 
    PSigma.mk p (PProd.mk Lp LNp)

class ByContradiction (L : Logic P) (lnot : Unar P) :=
  byContradiction : (p : P) ->
     ((L |- p) -> Contradiction L lnot) -> (L |- lnot p)

abbrev byContradiction {L : Logic P} {lnot}
  [K : ByContradiction L lnot] {p} := K.byContradiction p

--------------------------------------------------------------------------------
-- False
--------------------------------------------------------------------------------

class FalseImport (L : Logic P) (falsum : P) := 
  falseImport : False -> (L |- falsum) 

abbrev falseImport {L : Logic P} {falsum}
  [K : FalseImport L falsum] := K.falseImport

class FalseExport (L : Logic P) (falsum : P) := 
  falseExport : (L |- falsum) -> False

abbrev falseExport {L : Logic P} {falsum}
  [K : FalseExport L falsum] := K.falseExport

class AdFalsum (L : Logic P) (falsum : P) (lnot : Unar P) :=
  adFalsum : (p : P) -> ((L |- p) -> (L |- falsum)) -> (L |- ~p)

abbrev adFalsum {L : Logic P} {falsum : P} {lnot : Unar P}
  [K : AdFalsum L falsum lnot] {p} := K.adFalsum p

class ExFalsum (L : Logic P) (falsum : P) :=
  exFalsum : (p : P) -> (L |- falsum) -> (L |- p)

abbrev exFalsum {L : Logic P} {falsum}
  [K : ExFalsum L falsum] {p} := K.exFalsum p

end Gaea.Logic