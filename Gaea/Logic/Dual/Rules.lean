import Gaea.Logic.Judgment
import Gaea.Logic.Fun.Types

universes u w
variable {P : Sort u}

namespace Gaea.Logic

--------------------------------------------------------------------------------
-- Proof by Contraposition
-- (~q |- ~p) -> (|- p -> q)
--------------------------------------------------------------------------------

class ByContraposition (L : Logic P) (F : Binar P) (f : Unar P) :=
  toFun : (p q : P) -> ((L |- f q) -> (L |- f p)) -> (L |- F p q) 

abbrev byContraposition {L : Logic P} {F f}
  [K : ByContraposition L F f] {p q} := K.toFun p q

--------------------------------------------------------------------------------
-- Modus Tollens
--------------------------------------------------------------------------------

-- F p q, f p |- q 

class LeftMt (L : Logic P) (F : Binar P) (f : Unar P) :=
  toFun : (p q : P) -> (L |- F p q) -> (L |- f p) -> (L |- f q) 

abbrev leftMt {L : Logic P} {F f} 
  [K : LeftMt L F f] {p q} := K.toFun p q

abbrev mtr {L : Logic P} {F f} 
  [K : LeftMt L F f] {p q} := K.toFun p q

-- F p q, f q |- ~p 

class RightMt (L : Logic P) (F : Binar P) (f : Unar P) :=
  toFun : (p q : P) -> (L |- F p q) -> (L |- f q) -> (L |- f p)

abbrev rightMt {L : Logic P} {F f} 
  [K : RightMt L F f] {p q} := K.toFun p q

abbrev ModusTollens (L : Logic P) (F : Binar P) (f : Unar P)
  := RightMt L F f

abbrev mt {L : Logic P} {F f} 
  [K : RightMt L F f] {p q} := K.toFun p q

--------------------------------------------------------------------------------
-- Modus Tollendo Ponens
--------------------------------------------------------------------------------

-- F p q, f p |- q

class LeftMtp (L : Logic P) (F : Binar P) (f : Unar P) := 
  toFun : (p q : P) -> (L |- F p q) -> (L |- f p) -> (L |- q)

abbrev leftMtp {L : Logic P} {F} {f : Unar P} 
  [K : LeftMtp L F f] {p q} := K.toFun p q

abbrev ModusTollendoPonens (L : Logic P) (F : Binar P) (f : Unar P)
  := LeftMtp L F f

abbrev mtp {L : Logic P} {F} {f : Unar P} 
  [K : LeftMtp L F f] {p q} := K.toFun p q

-- F p q, f q |- p

class RightMtp (L : Logic P) (F : Binar P) (f : Unar P) := 
  toFun : (p q : P) -> (L |- F p q) -> (L |- f q) -> (L |- p)

abbrev rightMtp {L : Logic P} {F} {f : Unar P} 
  [K : RightMtp L F f] {p q} := K.toFun p q

abbrev mtpr {L : Logic P} {F} {f : Unar P} 
  [K : RightMtp L F f] {p q} := K.toFun p q

--------------------------------------------------------------------------------
-- Contradiction
--------------------------------------------------------------------------------

def Contradiction (L : Logic P) (f : Unar P) :=
  PSigma fun (p : P) => PProd (L |- f p) (L |- p) 

def contradiction {L : Logic P} {f}
  {p} (LNp : L |- f p) (Lp : L |- p) : Contradiction L f := 
    PSigma.mk p (PProd.mk LNp Lp)

-- Proof by Contradiction
-- ((|- p) -> Contradiction) -> (|- f p)

class ByContradiction (L : Logic P) (f : Unar P) :=
  toFun : (p : P) -> ((L |- p) -> Contradiction L f) -> (L |- f p)

abbrev byContradiction {L : Logic P} {f}
  [K : ByContradiction L f] {p} := K.toFun p

--------------------------------------------------------------------------------
-- Falsity
--------------------------------------------------------------------------------

-- Not |- p, ~p

class Noncontradiction (L : Logic P) (f : Unar P) := 
  toFun : (p : P) -> (L |- f p) -> (L |- p) -> False

abbrev noncontradiction {L : Logic P} {f} 
  [K : Noncontradiction L f] {p} := K.toFun p

-- ((|- p) -> False) -> (|- f p)

class AdFalso (L : Logic P) (f : Unar P) := 
  toFun : (p : P) -> ((L |- p) -> False) -> (L |- f p) 

abbrev adFalso {L : Logic P} {f}
  [K : AdFalso L f] {p} := K.toFun p

-- (p |- falsum) -> (|- f p)

class AdFalsum (L : Logic P) (falsum : P) (f : Unar P) :=
  toFun : (p : P) -> ((L |- p) -> (L |- falsum)) -> (L |- f p)

abbrev adFalsum {L : Logic P} {falsum : P} {f : Unar P}
  [K : AdFalsum L falsum f] {p} := K.toFun p

-- Principle of Explosion
-- (|- falsum) -> (|- p)

class ExFalsum (L : Logic P) (falsum : P) :=
  toFun : (p : P) -> (L |- falsum) -> (L |- p)

abbrev exFalsum {L : Logic P} {falsum}
  [K : ExFalsum L falsum] {p} := K.toFun p

--------------------------------------------------------------------------------
-- Double Negation
--------------------------------------------------------------------------------

-- p |- f (f p)

class DblNegIntro (L : Logic P) (f : Unar P) :=
  toFun : (p : P) -> (L |- p) -> (L |- f (f p))

abbrev dblNegIntro {L : Logic P} {f}
  [K : DblNegIntro L f] {p} := K.toFun p

-- f (f p) |- p

class DblNegElim (L : Logic P) (f : Unar P) :=
  toFun : (p : P) -> (L |- f (f p)) -> (L |- p)

abbrev dblNegElim {L : Logic P} {f}
  [K : DblNegElim L f] {p} := K.toFun p

end Gaea.Logic