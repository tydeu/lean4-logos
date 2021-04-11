import Gaea.Logic.Fun.Types
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
-- Basic Proof Rules
--------------------------------------------------------------------------------

-- Conditional Proof
-- (p |- q) -> (|- p -> q) 

class ByImplication (L : Logic P) (imp : Binar P) := 
  byImplication : (p q : P) -> ((L |- p) -> (L |- q)) -> (L |- p -> q) 

abbrev byImplication {L : Logic P} {imp} 
  [K : ByImplication L imp] {p q} := K.byImplication p q

-- Proof by Contraposition
-- (~q |- ~p) -> (|- p -> q)

class ByContraposition (L : Logic P) (imp : Binar P) (lnot : Unar P) :=
  byContraposition : (p q : P) -> ((L |- ~q) -> (L |- ~p)) -> (L |- p -> q) 

abbrev byContraposition {L : Logic P} {imp lnot}
  [K : ByContraposition L imp lnot] {p q} := K.byContraposition p q

-- Biconditional Proof
-- (p |- q) -> (q |- p) -> (|- p <-> q)

class Bicondition (L : Logic P) (iff : Binar P) := 
  bicondition : (p q : P) -> 
    ((L |- p) -> (L |- q)) -> ((L |- q) -> (L |- p)) -> (L |- p <-> q)

abbrev bicondition {L : Logic P} {iff}
  [K : Bicondition L iff] {p q} := K.bicondition p q

-- Conjunctive Proof
-- p, q |- p /\ q

class Conjunction (L : Logic P) (C : Binar P) := 
  conjoin : (p q : P) -> (L |- p) -> (L |- q) -> (L |- C p q) 

abbrev conjoin {L : Logic P} {C} 
  [K : Conjunction L C] {p q} := K.conjoin p q

-- Proof by Cases
-- (|- p \/ q) -> ((|- p) -> r) -> ((|- q) -> r) -> r

class ByEither (L : Logic P) (disj : Binar P) := 
  byEither : (r : Sort w) -> (p q : P) -> 
    (L |- p \/ q) -> ((L |- p) -> r) -> ((L |- q) -> r) -> r

abbrev byEither {L : Logic P} {disj}
  [K : ByEither L disj] {r p q} := K.byEither r p q

--------------------------------------------------------------------------------
-- Modus Ponens
--------------------------------------------------------------------------------

-- p <-> q, p |- q

class ModusPonens (L : Logic P) (iff : Binar P) := 
  mp : (p q : P) -> (L |- p <-> q) -> (L |- p) -> (L |- q)

abbrev mp {L : Logic P} {iff} 
  [K : ModusPonens L iff] {p q} := K.mp p q

abbrev mpl {L : Logic P} {iff} 
  [K : ModusPonens L iff] {p q} := K.mp p q

-- p <-> q, q |- p

class ModusPonensRev (L : Logic P) (iff : Binar P) := 
  mp : (p q : P) -> (L |- p <-> q) -> (L |- q) -> (L |- p)

abbrev mpr {L : Logic P} {iff} 
  [K : ModusPonensRev L iff] {p q} := K.mp p q

--------------------------------------------------------------------------------
-- Modus Tollens
--------------------------------------------------------------------------------

-- p <-> q, ~q |- ~p 

class ModusTollens (L : Logic P) (iff : Binar P) (lnot : Unar P) :=
  mt : (p q : P) -> (L |- p <-> q) -> (L |- ~q) -> (L |- ~p)

abbrev mt {L : Logic P} {iff lnot} 
  [K : ModusTollens L iff lnot] {p q} := K.mt p q

abbrev mtr {L : Logic P} {iff lnot} 
  [K : ModusTollens L iff lnot] {p q} := K.mt p q

-- p <-> q, ~p |- q 

class ModusTollensRev (L : Logic P) (iff : Binar P) (lnot : Unar P) :=
  mt : (p q : P) -> (L |- p <-> q) -> (L |- ~p) -> (L |- ~q) 

abbrev mtl {L : Logic P} {iff lnot} 
  [K : ModusTollensRev L iff lnot] {p q} := K.mt p q

--------------------------------------------------------------------------------
-- Modus Tollendo Ponens / Disjunctive Syllogism
--------------------------------------------------------------------------------

-- p \/ q, ~p |- q

class LeftNeg (L : Logic P) (D : Binar P) (lnot : Unar P) := 
  leftNeg : (p q : P) -> (L |- D p q) -> (L |- ~p) -> (L |- q)

abbrev leftNeg {L : Logic P} {D} {lnot : Unar P} 
  [K : LeftNeg L D lnot] {p q} := K.leftNeg p q

-- p \/ q, ~q |- p

class RightNeg (L : Logic P) (D : Binar P) (lnot : Unar P) := 
  rightNeg : (p q : P) -> (L |- D p q) -> (L |- ~q) -> (L |- p)

abbrev rightNeg {L : Logic P} {D} {lnot : Unar P} 
  [K : RightNeg L D lnot] {p q} := K.rightNeg p q

--------------------------------------------------------------------------------
-- Simplification
--------------------------------------------------------------------------------

-- C p p |- p

class Simplification (L : Logic P) (C : Binar P)  :=
  simp : (p : P) -> (L |- C p p) -> (L |- p)

abbrev simp {L : Logic P} {C} 
  [K : Simplification L C] {p} := K.simp p

instance iSimpOfByEither {L : Logic P} {D}
  [K : ByEither L D] : Simplification L D := 
  {simp := fun p LpDp => K.byEither _ p p LpDp id id}

-- C p q |- p

class LeftSimp (L : Logic P) (C : Binar P) := 
  leftSimp : (p q : P) -> (L |- C p q) -> (L |- p)

abbrev leftSimp {L : Logic P} {conj} 
  [K : LeftSimp L conj] {p q} := K.leftSimp p q

instance iSimpOfLeft {L : Logic P} {conj}
  [K : LeftSimp L conj] : Simplification L conj := 
  {simp := fun p LpCq => K.leftSimp p p LpCq}

-- C p q |- q

class RightSimp (L : Logic P) (C : Binar P) := 
  rightSimp : (p q : P) -> (L |- C p q) -> (L |- q)

abbrev rightSimp {L : Logic P} {conj} 
  [K : RightSimp L conj] {p q} := K.rightSimp p q

instance iSimpOfRight {L : Logic P} {conj}
  [K : RightSimp L conj] : Simplification L conj := 
  {simp := fun p LpCq => K.rightSimp p p LpCq}

--------------------------------------------------------------------------------
-- Currying
--------------------------------------------------------------------------------

-- (p /\ q -> a) -> (p -> q -> a)

class Curry (L : Logic P) (C : Binar P) :=
  curry : (r : Sort w) -> (p q : P) -> 
    ((L |- C p q) -> r) -> ((L |- p) -> (L |- q) -> r)

abbrev curry {L : Logic P} {C} 
  [K : Curry L C] {r p q} := K.curry r p q

instance iCurryOfConjunction {L : Logic P} {C}
  [K : Conjunction L C] : Curry L C := 
  {curry := fun a p q fpCq Lp Lq  => fpCq (conjoin Lp Lq)}

instance iConjunctionOfCurry {L : Logic P} {C}
  [K : Curry L C] : Conjunction L C := 
  {conjoin := fun p q => K.curry _ p q id}

-- (p -> q -> a) -> (p /\ q -> a)

class Uncurry (L : Logic P) (conj : Binar P) :=
  uncurry : (r : Sort w) -> (p q : P) -> 
    ((L |- p) -> (L |- q) -> r) -> ((L |- p /\ q) -> r)

abbrev uncurry {L : Logic P} {conj} 
  [K : Uncurry L conj] {r p q} := K.uncurry r p q

instance iUncurryOfLeftRightSimp {L : Logic P} {conj}
  [CjL : LeftSimp L conj] [CjR : RightSimp L conj] : Uncurry L conj := 
  {uncurry := fun a p q fpq LpCq => fpq (leftSimp LpCq) (rightSimp LpCq)}

instance iLeftSimpOfUncurry {L : Logic P} {conj}
  [K : Uncurry L conj] : LeftSimp L conj := 
  {leftSimp := fun p q => K.uncurry _ p q (fun Lp Lq => Lp)}

instance iRightSimpOfUncurry {L : Logic P} {conj}
  [K : Uncurry L conj] : RightSimp L conj := 
  {rightSimp := fun p q => K.uncurry _ p q (fun Lp Lq => Lq)}

--------------------------------------------------------------------------------
-- Tautology
--------------------------------------------------------------------------------

-- p |- D p p

class Tautology (L : Logic P) (D : Binar P)  :=
  taut : (p : P) -> (L |- p) -> (L |- D p p)

abbrev taut {L : Logic P} {D} 
  [K : Tautology L D] {p} := K.taut p

instance iTautOfConjunction {L : Logic P} {C}
  [K : Conjunction L C] : Tautology L C := 
  {taut := fun p Lp => K.conjoin p p Lp Lp}

-- p |- D p q

class LeftTaut (L : Logic P) (D : Binar P)  := 
  leftTaut : (p q : P) -> (L |- p) -> (L |- D p q) 

abbrev leftTaut {L : Logic P} {D} 
  [K : LeftTaut L D] {p q} := K.leftTaut p q

instance iTautOfLeft {L : Logic P} {D}
  [K : LeftTaut L D] : Tautology L D := 
  {taut := fun p Lp => K.leftTaut p p Lp}

-- q |- D p q

class RightTaut (L : Logic P) (D : Binar P)  := 
  rightTaut : (p q : P) -> (L |- q) -> (L |- D p q) 

abbrev rightTaut {L : Logic P} {D} 
  [K : RightTaut L D] {p q} := K.rightTaut p q

instance iTautOfRight {L : Logic P} {D}
  [K : RightTaut L D] : Tautology L D := 
  {taut := fun p Lp => K.rightTaut p p Lp}

--------------------------------------------------------------------------------
-- Contradiction
--------------------------------------------------------------------------------

def Contradiction (L : Logic P) (lnot : Unar P) :=
  PSigma fun (p : P) => PProd (L |- lnot p) (L |- p) 

def contradiction {L : Logic P} {lnot}
  {p} (LNp : L |- lnot p) (Lp : L |- p) : Contradiction L lnot := 
    PSigma.mk p (PProd.mk LNp Lp)

-- Proof by Contradiction
-- ((|- p) -> Contradiction) -> (|- ~p)

class ByContradiction (L : Logic P) (lnot : Unar P) :=
  byContradiction : (p : P) ->
     ((L |- p) -> Contradiction L lnot) -> (L |- lnot p)

abbrev byContradiction {L : Logic P} {lnot}
  [K : ByContradiction L lnot] {p} := K.byContradiction p

--------------------------------------------------------------------------------
-- Falsity
--------------------------------------------------------------------------------

-- Not |- p, ~p

class Noncontradiction (L : Logic P) (lnot : Unar P) := 
  noncontradiction : (p : P) -> (L |- ~p) -> (L |- p) -> False

abbrev noncontradiction {L : Logic P} {lnot} 
  [K : Noncontradiction L lnot] {p} := K.noncontradiction p

-- ((|- p) -> False) -> (|- ~p)

class AdFalso (L : Logic P) (lnot : Unar P) := 
  adFalso : (p : P) -> ((L |- p) -> False) -> (L |- ~p) 

abbrev adFalso {L : Logic.{u,0} P} {lnot}
  [K : AdFalso L lnot] {p} := K.adFalso p

-- (p |- falsum) -> (|- ~p)

class AdFalsum (L : Logic P) (falsum : P) (lnot : Unar P) :=
  adFalsum : (p : P) -> ((L |- p) -> (L |- falsum)) -> (L |- ~p)

abbrev adFalsum {L : Logic P} {falsum : P} {lnot : Unar P}
  [K : AdFalsum L falsum lnot] {p} := K.adFalsum p

-- (|- falsum) -> (|- p)

class ExFalsum (L : Logic P) (falsum : P) :=
  exFalsum : (p : P) -> (L |- falsum) -> (L |- p)

abbrev exFalsum {L : Logic P} {falsum}
  [K : ExFalsum L falsum] {p} := K.exFalsum p

--------------------------------------------------------------------------------
-- Double Negation
--------------------------------------------------------------------------------

-- p |- ~~p

class DblNegIntro (L : Logic P) (lnot : Unar P) :=
  dblNegIntro : (p : P) -> (L |- p) -> (L |- ~~p)

abbrev dblNegIntro {L : Logic P} {lnot}
  [K : DblNegIntro L lnot] {p} := K.dblNegIntro p

-- ~~p |- p

class DblNegElim (L : Logic P) (lnot : Unar P) :=
  dblNegElim : (p : P) -> (L |- ~~p) -> (L |- p)

abbrev dblNegElim {L : Logic P} {lnot}
  [K : DblNegElim L lnot] {p} := K.dblNegElim p

end Gaea.Logic