import Gaea.Logic.Judgment
import Gaea.Logic.Fun.Types

namespace Gaea.Logic

universe u
variable {P : Sort u} 

--------------------------------------------------------------------------------
-- Commutativity
--------------------------------------------------------------------------------

-- C p q <-> C q p

class Comm (L : Logic P) (C : Binar P) :=
  comm : (p q : P) -> (L |- C p q) -> (L |- C q p)

abbrev comm {L : Logic P} {C} 
  [K : Comm L C] {p q} := K.comm p q

--------------------------------------------------------------------------------
-- Associativity
--------------------------------------------------------------------------------

-- C (C p q) r <-> C p (C q r)

class LtrAssoc (L : Logic P) (C : Binar P) :=
  ltrAssoc : (p q r : P) -> (L |- C (C p q) r) -> (L |- C p (C q r))

abbrev ltrAssoc {L : Logic P} {C} 
  [K : LtrAssoc L C] {p q r} := K.ltrAssoc p q r

class RtlAssoc (L : Logic P) (C : Binar P) :=
  rtlAssoc : (p q r : P) -> (L |- C p (C q r)) -> (L |- C (C p q) r)

abbrev rtlAssoc {L : Logic P} {C}
  [K : RtlAssoc L C] {p q r} := K.rtlAssoc p q r

--------------------------------------------------------------------------------
-- Distributivity
--------------------------------------------------------------------------------

-- C p (G q r) -> C (G p q) (G p r)

class LeftDistrib (L : Logic P) (C : Binar P) (G : Binar P) :=
  leftDistrib : (p q r : P) -> (L |- C p (G q r)) -> (L |- G (C p q) (C p r))

abbrev leftDistrib {L : Logic P} {C G}
  [K : LeftDistrib L C G] {p q r} := K.leftDistrib p q r

-- C (G q r) p -> C (G q p) (G r p)

class RightDistrib (L : Logic P) (C : Binar P) (G : Binar P) :=
  rightDistrib : (p q r : P) -> (L |- C (G q r) p) -> (L |- G (C q p) (C r p))

abbrev rightDistrib {L : Logic P} {C G}
  [K : RightDistrib L C G] {p q r} := K.rightDistrib p q r

end Gaea.Logic