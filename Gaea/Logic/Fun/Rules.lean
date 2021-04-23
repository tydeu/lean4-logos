import Gaea.Logic.Judgment
import Gaea.Logic.Fun.Types
import Gaea.Logic.Rel.Rules

namespace Gaea.Logic

universe u
variable {P : Sort u} 

--------------------------------------------------------------------------------
-- Commutativity
--------------------------------------------------------------------------------

-- F p q <-> F q p

class Comm (L : Logic P) (F : Binar P) :=
  toFun : (p q : P) -> (L |- F p q) -> (L |- F q p)

abbrev comm {L : Logic P} {F} 
  [K : Comm L F] {p q} := K.toFun p q

instance iSymmOfComm {L : Logic P} {R : Rel P P}
  [K : Comm L R] : Symm L R := {toFun := K.toFun}

instance iCommOfSymm {L : Logic P} {R : Rel P P}
  [K : Symm L R] : Comm L R := {toFun := K.toFun}

--------------------------------------------------------------------------------
-- Associativity
--------------------------------------------------------------------------------

-- F (F p q) r <-> F p (F q r)

class LtrAssoc (L : Logic P) (F : Binar P) :=
  toFun : (p q r : P) -> (L |- F (F p q) r) -> (L |- F p (F q r))

abbrev ltrAssoc {L : Logic P} {F} 
  [K : LtrAssoc L F] {p q r} := K.toFun p q r

class RtlAssoc (L : Logic P) (F : Binar P) :=
  toFun : (p q r : P) -> (L |- F p (F q r)) -> (L |- F (F p q) r)

abbrev rtlAssoc {L : Logic P} {F}
  [K : RtlAssoc L F] {p q r} := K.toFun p q r

--------------------------------------------------------------------------------
-- Distributivity
--------------------------------------------------------------------------------

-- F p (G q r) -> F (G p q) (G p r)

class LeftDistrib (L : Logic P) (F : Binar P) (G : Binar P) :=
  toFun : (p q r : P) -> (L |- F p (G q r)) -> (L |- G (F p q) (F p r))

abbrev leftDistrib {L : Logic P} {F G}
  [K : LeftDistrib L F G] {p q r} := K.toFun p q r

-- F (G q r) p -> F (G q p) (G r p)

class RightDistrib (L : Logic P) (F : Binar P) (G : Binar P) :=
  toFun : (p q r : P) -> (L |- F (G q r) p) -> (L |- G (F q p) (F r p))

abbrev rightDistrib {L : Logic P} {F G}
  [K : RightDistrib L F G] {p q r} := K.toFun p q r

--------------------------------------------------------------------------------
-- Tautology
--------------------------------------------------------------------------------

-- p |- F p p

class Taut (L : Logic P) (F : Binar P)  :=
  toFun : (p : P) -> (L |- p) -> (L |- F p p)

abbrev taut {L : Logic P} {F} 
  [K : Taut L F] {p} := K.toFun p

instance iTautOfRefl {L : Logic P} {R} 
  [K : Refl L R] : Taut L R := {toFun := fun p Lp => K.toFun p}

-- p |- F p q

class LeftTaut (L : Logic P) (F : Binar P)  := 
  toFun : (p q : P) -> (L |- p) -> (L |- F p q) 

abbrev leftTaut {L : Logic P} {F} 
  [K : LeftTaut L F] {p q} := K.toFun p q

instance iTautOfLeft {L : Logic P} {F}
  [K : LeftTaut L F] : Taut L F := 
  {toFun := fun p Lp => K.toFun p p Lp}

-- q |- F p q

class RightTaut (L : Logic P) (F : Binar P)  := 
  toFun : (p q : P) -> (L |- q) -> (L |- F p q) 

abbrev rightTaut {L : Logic P} {F} 
  [K : RightTaut L F] {p q} := K.toFun p q

instance iTautOfRight {L : Logic P} {F}
  [K : RightTaut L F] : Taut L F := 
  {toFun := fun p Lp => K.toFun p p Lp}

--------------------------------------------------------------------------------
-- Simplification
--------------------------------------------------------------------------------

-- F p p |- p

class Simp (L : Logic P) (F : Binar P)  :=
  toFun : (p : P) -> (L |- F p p) -> (L |- p)

abbrev simp {L : Logic P} {F} 
  [K : Simp L F] {p} := K.toFun p

-- F p q |- p

class LeftSimp (L : Logic P) (F : Binar P) := 
  toFun : (p q : P) -> (L |- F p q) -> (L |- p)

abbrev leftSimp {L : Logic P} {F} 
  [K : LeftSimp L F] {p q} := K.toFun p q

instance iSimpOfLeft {L : Logic P} {F}
  [K : LeftSimp L F] : Simp L F := 
  {toFun := fun p LpCq => K.toFun p p LpCq}

-- F p q |- q

class RightSimp (L : Logic P) (F : Binar P) := 
  toFun : (p q : P) -> (L |- F p q) -> (L |- q)

abbrev rightSimp {L : Logic P} {F} 
  [K : RightSimp L F] {p q} := K.toFun p q

instance iSimpOfRight {L : Logic P} {F}
  [K : RightSimp L F] : Simp L F := 
  {toFun := fun p LpCq => K.toFun p p LpCq}

--------------------------------------------------------------------------------
-- Currying
--------------------------------------------------------------------------------

-- (|- F p q) -> r -> ((|- p) -> (|- q) -> r)

class Curry (L : Logic P) (F : Binar P) :=
  toFun : (r : Sort w) -> (p q : P) -> 
    ((L |- F p q) -> r) -> ((L |- p) -> (L |- q) -> r)

abbrev curry {L : Logic P} {F} 
  [K : Curry L F] {r p q} := K.toFun r p q

-- ((|- p) -> (|- q) -> r) -> ((|- F p q) -> r)

class Uncurry (L : Logic P) (F : Binar P) :=
  toFun : (r : Sort w) -> (p q : P) -> 
    ((L |- p) -> (L |- q) -> r) -> ((L |- F p q) -> r)

abbrev uncurry {L : Logic P} {F} 
  [K : Uncurry L F] {r p q} := K.toFun r p q

instance iUncurryOfLeftRightSimp {L : Logic P} {F}
  [CjL : LeftSimp L F] [CjR : RightSimp L F] : Uncurry L F := 
  {toFun := fun a p q fpq LpCq => fpq (leftSimp LpCq) (rightSimp LpCq)}

instance iLeftSimpOfUncurry {L : Logic P} {F}
  [K : Uncurry L F] : LeftSimp L F := 
  {toFun := fun p q => K.toFun _ p q (fun Lp Lq => Lp)}

instance iRightSimpOfUncurry {L : Logic P} {F}
  [K : Uncurry L F] : RightSimp L F := 
  {toFun := fun p q => K.toFun _ p q (fun Lp Lq => Lq)}
