import Gaea.Logic.Notation

namespace Gaea.Logic

universe u
variable {P : Sort u} (L : Logic P) (F : P -> P -> P)

-- Reflexivity
-- p |- F p p

class LRefl :=
  lRefl : (p : P) -> (L |- p) -> (L |- F p p)

def lRefl {L F} [K :  LRefl L F] {p : P} := K.lRefl p

-- Commutativity
-- F p q -|- F q p

class LComm :=
  lComm : (p q : P) -> (L |- F p q) -> (L |- F q p)

def lComm {L F} [K :  LComm L F] {p q : P} := K.lComm p q

-- Associativity
-- F (F p q) r -|- F p (F q r)

class LAssocLtr :=
  lAssocLtr : (p q r : P) -> (L |- F (F p q) r) -> (L |- F p (F q r))

def lAssocLtr {L F} [K :  LAssocLtr L F] {p q r : P} := K.lAssocLtr p q r

class LAssocRtl :=
  lAssocRtl : (p q r : P) -> (L |- F p (F q r)) -> (L |- F (F p q) r)

def lAssocRtl {L F} [K :  LAssocRtl L F] {p q r : P} := K.lAssocRtl p q r

-- (Self-)Distributivity
-- F (F p q) r -|- F p (F q r)

class LLeftDistr :=
  lLeftDistr : (p q r : P) -> (L |- F p (F q r)) -> (L |- F (F p q) (F p r))

def lLeftDistr {L F} [K :  LLeftDistr L F] {p q r : P} := K.lLeftDistr p q r

class LRightDistr :=
  lRightDistr : (p q r : P) -> (L |- F (F q r) p) -> (L |- F (F q p) (F r p))

def lRightDistr {L F} [K :  LRightDistr L F] {p q r : P} := K.lRightDistr p q r

end Gaea.Logic