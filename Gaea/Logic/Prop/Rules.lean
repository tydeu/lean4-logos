import Gaea.Logic.Fun.Types
import Gaea.Logic.Judgment
import Gaea.Logic.Prop.Syntax
import Gaea.Logic.Prop.Notation

universes u w
variable {P : Sort u}

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

class Condition (L : Logic P) (imp : Binar P) := 
  condition : (p q : P) -> ((L |- p) -> (L |- q)) -> (L |- p -> q) 

abbrev condition {L : Logic P} {imp} 
  [K : Condition L imp] {p q} := K.condition p q

-- Proof by Contraposition
-- (~q |- ~p) -> (|- p -> q)

class ByContraposition (L : Logic P) (imp : Binar P) (lneg : Unar P) :=
  byContraposition : (p q : P) -> ((L |- ~q) -> (L |- ~p)) -> (L |- p -> q) 

abbrev byContraposition {L : Logic P} {imp lneg}
  [K : ByContraposition L imp lneg] {p q} := K.byContraposition p q

-- Biconditional Proof
-- (p |- q) -> (q |- p) -> (|- p <-> q)

class Bicondition (L : Logic P) (iff : Binar P) := 
  bicondition : (p q : P) -> 
    ((L |- p) -> (L |- q)) -> ((L |- q) -> (L |- p)) -> (L |- p <-> q)

abbrev bicondition {L : Logic P} {iff}
  [K : Bicondition L iff] {p q} := K.bicondition p q

-- Conjunctive Proof
-- p, q |- p /\ q

class Conjoin (L : Logic P) (C : Binar P) := 
  conjoin : (p q : P) -> (L |- p) -> (L |- q) -> (L |- C p q) 

abbrev conjoin {L : Logic P} {C} 
  [K : Conjoin L C] {p q} := K.conjoin p q

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

class LeftMp (L : Logic P) (iff : Binar P) := 
  mp : (p q : P) -> (L |- p <-> q) -> (L |- p) -> (L |- q)

abbrev leftMp {L : Logic P} {iff} 
  [K : LeftMp L iff] {p q} := K.mp p q

abbrev ModusPonens (L : Logic P) (imp : Binar P) 
  := LeftMp L imp

abbrev mp {L : Logic P} {imp} 
  [K : LeftMp L imp] {p q} := K.mp p q

-- p <-> q, q |- p

class RightMp (L : Logic P) (iff : Binar P) := 
  mp : (p q : P) -> (L |- p <-> q) -> (L |- q) -> (L |- p)

abbrev rightMp {L : Logic P} {iff} 
  [K : RightMp L iff] {p q} := K.mp p q

abbrev mpr {L : Logic P} {iff} 
  [K : RightMp L iff] {p q} := K.mp p q


--------------------------------------------------------------------------------
-- Modus Tollens
--------------------------------------------------------------------------------

-- p <-> q, ~p |- q 

class LeftMt (L : Logic P) (iff : Binar P) (lneg : Unar P) :=
  mt : (p q : P) -> (L |- p <-> q) -> (L |- ~p) -> (L |- ~q) 

abbrev leftMt {L : Logic P} {iff lneg} 
  [K : LeftMt L iff lneg] {p q} := K.mt p q

abbrev mtr {L : Logic P} {iff lneg} 
  [K : LeftMt L iff lneg] {p q} := K.mt p q

-- p <-> q, ~q |- ~p 

class RightMt (L : Logic P) (iff : Binar P) (lneg : Unar P) :=
  mt : (p q : P) -> (L |- p <-> q) -> (L |- ~q) -> (L |- ~p)

abbrev rightMt {L : Logic P} {iff lneg} 
  [K : RightMt L iff lneg] {p q} := K.mt p q

abbrev ModusTollens (L : Logic P) (imp : Binar P) (lneg : Unar P)
  := RightMt L imp lneg

abbrev mt {L : Logic P} {imp lneg} 
  [K : RightMt L imp lneg] {p q} := K.mt p q


--------------------------------------------------------------------------------
-- Modus Tollendo Ponens
--------------------------------------------------------------------------------

-- p \/ q, ~p |- q

class LeftMtp (L : Logic P) (disj : Binar P) (lneg : Unar P) := 
  mtp : (p q : P) -> (L |- p \/ q) -> (L |- ~p) -> (L |- q)

abbrev leftMtp {L : Logic P} {disj} {lneg : Unar P} 
  [K : LeftMtp L disj lneg] {p q} := K.mtp p q

abbrev ModusTollendoPonens (L : Logic P) (imp : Binar P) (lneg : Unar P)
  := LeftMtp L imp lneg

abbrev mtp {L : Logic P} {disj} {lneg : Unar P} 
  [K : LeftMtp L disj lneg] {p q} := K.mtp p q

-- p \/ q, ~q |- p

class RightMtp (L : Logic P) (disj : Binar P) (lneg : Unar P) := 
  mtp : (p q : P) -> (L |- p \/ q) -> (L |- ~q) -> (L |- p)

abbrev rightMtp {L : Logic P} {disj} {lneg : Unar P} 
  [K : RightMtp L disj lneg] {p q} := K.mtp p q

abbrev mtpr {L : Logic P} {disj} {lneg : Unar P} 
  [K : RightMtp L disj lneg] {p q} := K.mtp p q

--------------------------------------------------------------------------------
-- Tautology
--------------------------------------------------------------------------------

-- p |- D p p

class Taut (L : Logic P) (D : Binar P)  :=
  taut : (p : P) -> (L |- p) -> (L |- D p p)

abbrev taut {L : Logic P} {D} 
  [K : Taut L D] {p} := K.taut p

instance iTautOfConjoin {L : Logic P} {C}
  [K : Conjoin L C] : Taut L C := 
  {taut := fun p Lp => K.conjoin p p Lp Lp}

-- p |- D p q

class LeftTaut (L : Logic P) (D : Binar P)  := 
  leftTaut : (p q : P) -> (L |- p) -> (L |- D p q) 

abbrev leftTaut {L : Logic P} {D} 
  [K : LeftTaut L D] {p q} := K.leftTaut p q

instance iTautOfLeft {L : Logic P} {D}
  [K : LeftTaut L D] : Taut L D := 
  {taut := fun p Lp => K.leftTaut p p Lp}

-- q |- D p q

class RightTaut (L : Logic P) (D : Binar P)  := 
  rightTaut : (p q : P) -> (L |- q) -> (L |- D p q) 

abbrev rightTaut {L : Logic P} {D} 
  [K : RightTaut L D] {p q} := K.rightTaut p q

instance iTautOfRight {L : Logic P} {D}
  [K : RightTaut L D] : Taut L D := 
  {taut := fun p Lp => K.rightTaut p p Lp}

--------------------------------------------------------------------------------
-- Simplification
--------------------------------------------------------------------------------

-- C p p |- p

class Simp (L : Logic P) (C : Binar P)  :=
  simp : (p : P) -> (L |- C p p) -> (L |- p)

abbrev simp {L : Logic P} {C} 
  [K : Simp L C] {p} := K.simp p

instance iSimpOfByEither {L : Logic P} {D}
  [K : ByEither L D] : Simp L D := 
  {simp := fun p LpDp => K.byEither _ p p LpDp id id}

-- C p q |- p

class LeftSimp (L : Logic P) (C : Binar P) := 
  leftSimp : (p q : P) -> (L |- C p q) -> (L |- p)

abbrev leftSimp {L : Logic P} {conj} 
  [K : LeftSimp L conj] {p q} := K.leftSimp p q

instance iSimpOfLeft {L : Logic P} {conj}
  [K : LeftSimp L conj] : Simp L conj := 
  {simp := fun p LpCq => K.leftSimp p p LpCq}

-- C p q |- q

class RightSimp (L : Logic P) (C : Binar P) := 
  rightSimp : (p q : P) -> (L |- C p q) -> (L |- q)

abbrev rightSimp {L : Logic P} {conj} 
  [K : RightSimp L conj] {p q} := K.rightSimp p q

instance iSimpOfRight {L : Logic P} {conj}
  [K : RightSimp L conj] : Simp L conj := 
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

instance iCurryOfConjoin {L : Logic P} {C}
  [K : Conjoin L C] : Curry L C := 
  {curry := fun a p q fpCq Lp Lq  => fpCq (conjoin Lp Lq)}

instance iConjoinOfCurry {L : Logic P} {C}
  [K : Curry L C] : Conjoin L C := 
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
-- Contradiction
--------------------------------------------------------------------------------

def Contradiction (L : Logic P) (lneg : Unar P) :=
  PSigma fun (p : P) => PProd (L |- lneg p) (L |- p) 

def contradiction {L : Logic P} {lneg}
  {p} (LNp : L |- lneg p) (Lp : L |- p) : Contradiction L lneg := 
    PSigma.mk p (PProd.mk LNp Lp)

-- Proof by Contradiction
-- ((|- p) -> Contradiction) -> (|- ~p)

class ByContradiction (L : Logic P) (lneg : Unar P) :=
  byContradiction : (p : P) ->
     ((L |- p) -> Contradiction L lneg) -> (L |- lneg p)

abbrev byContradiction {L : Logic P} {lneg}
  [K : ByContradiction L lneg] {p} := K.byContradiction p

--------------------------------------------------------------------------------
-- Falsity
--------------------------------------------------------------------------------

-- Not |- p, ~p

class Noncontradiction (L : Logic P) (lneg : Unar P) := 
  noncontradiction : (p : P) -> (L |- ~p) -> (L |- p) -> False

abbrev noncontradiction {L : Logic P} {lneg} 
  [K : Noncontradiction L lneg] {p} := K.noncontradiction p

-- ((|- p) -> False) -> (|- ~p)

class AdFalso (L : Logic P) (lneg : Unar P) := 
  adFalso : (p : P) -> ((L |- p) -> False) -> (L |- ~p) 

abbrev adFalso {L : Logic.{u,0} P} {lneg}
  [K : AdFalso L lneg] {p} := K.adFalso p

-- (p |- falsum) -> (|- ~p)

class AdFalsum (L : Logic P) (falsum : P) (lneg : Unar P) :=
  adFalsum : (p : P) -> ((L |- p) -> (L |- falsum)) -> (L |- ~p)

abbrev adFalsum {L : Logic P} {falsum : P} {lneg : Unar P}
  [K : AdFalsum L falsum lneg] {p} := K.adFalsum p

-- (|- falsum) -> (|- p)

class ExFalsum (L : Logic P) (falsum : P) :=
  exFalsum : (p : P) -> (L |- falsum) -> (L |- p)

abbrev exFalsum {L : Logic P} {falsum}
  [K : ExFalsum L falsum] {p} := K.exFalsum p

--------------------------------------------------------------------------------
-- Double Negation
--------------------------------------------------------------------------------

-- p |- ~~p

class DblNegIntro (L : Logic P) (lneg : Unar P) :=
  dblNegIntro : (p : P) -> (L |- p) -> (L |- ~~p)

abbrev dblNegIntro {L : Logic P} {lneg}
  [K : DblNegIntro L lneg] {p} := K.dblNegIntro p

-- ~~p |- p

class DblNegElim (L : Logic P) (lneg : Unar P) :=
  dblNegElim : (p : P) -> (L |- ~~p) -> (L |- p)

abbrev dblNegElim {L : Logic P} {lneg}
  [K : DblNegElim L lneg] {p} := K.dblNegElim p

end Gaea.Logic