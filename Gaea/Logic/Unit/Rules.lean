import Gaea.Logic.Judgment
import Gaea.Logic.Fun.Rules

universes u w
variable {P : Sort u}

namespace Gaea

--------------------------------------------------------------------------------
-- Postulate
-- |- p
--------------------------------------------------------------------------------

class Postulate (L : Logic P) (p : P) := 
  toProof : L |- p

abbrev postulate {L : Logic P} {p}
  [K : Postulate L p] := K.toProof

--------------------------------------------------------------------------------
-- Conjunctive Proof
-- p, q |- F p q
--------------------------------------------------------------------------------

class Conjoin (L : Logic P) (F : Binar P) := 
  toFun : (p q : P) -> (L |- p) -> (L |- q) -> (L |- F p q) 

abbrev conjoin {L : Logic P} {F} 
  [K : Conjoin L F] {p q} := K.toFun p q

instance iCurryOfConjoin {L : Logic P} {F}
  [K : Conjoin L F] : Curry L F := 
  {toFun := fun a p q fpCq Lp Lq  => fpCq (K.toFun p q Lp Lq)}

instance iConjoinOfCurry {L : Logic P} {F}
  [K : Curry L F] : Conjoin L F := 
  {toFun := fun p q => K.toFun _ p q id}

instance iTautOfConjoin {L : Logic P} {F}
  [K : Conjoin L F] : Taut L F := 
  {toFun := fun p Lp => K.toFun p p Lp Lp}

--------------------------------------------------------------------------------
-- Disjunctive Proof (Proof by Cases)
-- (|- F p q) -> ((|- p) -> r) -> ((|- q) -> r) -> r
--------------------------------------------------------------------------------

class ByEither (L : Logic P) (F : Binar P) := 
  toFun : (p q : P) -> (L |- F p q) -> 
    (r : Sort w) -> ((L |- p) -> r) -> ((L |- q) -> r) -> r

abbrev byEither {L : Logic P} {F}
  [K : ByEither L F] {p q} (Fpq) {r} := K.toFun p q Fpq r

instance iSimpOfByEither {L : Logic P} {F}
  [K : ByEither L F] : Simp L F := 
  {toFun := fun p LpDp => K.toFun p p LpDp _ id id}

--------------------------------------------------------------------------------
-- Conditional Proof
--------------------------------------------------------------------------------

-- Left Condition
-- (p |- q) -> (|- F p q) 

class LeftCond (L : Logic P) (F : Binar P) := 
  toFun : (p q : P) -> ((L |- p) -> (L |- q)) -> (L |- F p q) 

abbrev leftCond {L : Logic P} {F} 
  [K : LeftCond L F] {p q} := K.toFun p q

abbrev Condition (L : Logic P) (F : Binar P) 
  := LeftCond L F

abbrev condition {L : Logic P} {F} 
  [K : Condition L F] {p q} := K.toFun p q

instance iReflOfLeftCond {L : Logic P} {F} 
  [K : Condition L F] : Refl L F := 
  {toFun := fun p => K.toFun p p id}

instance iRightTautOfLeftCond {L : Logic P} {F} 
  [K : Condition L F] : RightTaut L F := 
  {toFun := fun p q Lq => K.toFun p q (fun Lp => Lq)}

-- Right Condition
-- (q |- p) -> (|- F p q) 

class RightCond (L : Logic P) (F : Binar P) := 
  toFun : (p q : P) -> ((L |- q) -> (L |- p)) -> (L |- F p q) 

abbrev rightCond {L : Logic P} {F} 
  [K : RightCond L F] {p q} := K.toFun p q

instance iReflOfRightCond {L : Logic P} {F} 
  [K : RightCond L F] : Refl L F := 
  {toFun := fun p => K.toFun p p id}

instance iLeftTautOfRightCond {L : Logic P} {F} 
  [K : RightCond L F] : LeftTaut L F := 
  {toFun := fun p q Lp => K.toFun p q (fun Lq => Lp)}

--------------------------------------------------------------------------------
-- Biconditional Proof
-- (p |- q) -> (q |- p) -> (|- F p q)
--------------------------------------------------------------------------------

class Bicondition (L : Logic P) (F : Binar P) := 
  toFun : (p q : P) -> 
    ((L |- p) -> (L |- q)) -> ((L |- q) -> (L |- p)) -> (L |- F p q)

abbrev bicondition {L : Logic P} {F}
  [K : Bicondition L F] {p q} := K.toFun p q

instance iReflOfBicondition {L : Logic P} {F} 
  [K : Bicondition L F] : Refl L F := 
  {toFun := fun p => K.toFun p p id id}

--------------------------------------------------------------------------------
-- Modus Ponens
--------------------------------------------------------------------------------

-- F p q, p |- q

class LeftMp (L : Logic P) (F : Binar P) := 
  toFun : (p q : P) -> (L |- F p q) -> (L |- p) -> (L |- q)

abbrev leftMp {L : Logic P} {F} 
  [K : LeftMp L F] {p q} := K.toFun p q

abbrev ModusPonens (L : Logic P) (F : Binar P) 
  := LeftMp L F

abbrev mp {L : Logic P} {F} 
  [K : LeftMp L F] {p q} := K.toFun p q

-- F p q, q |- p

class RightMp (L : Logic P) (F : Binar P) := 
  toFun : (p q : P) -> (L |- F p q) -> (L |- q) -> (L |- p)

abbrev rightMp {L : Logic P} {F} 
  [K : RightMp L F] {p q} := K.toFun p q

abbrev mpr {L : Logic P} {F} 
  [K : RightMp L F] {p q} := K.toFun p q
