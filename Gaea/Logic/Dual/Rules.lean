import Gaea.Logic.Judgment
import Gaea.Logic.Fun.Types
import Gaea.Logic.Prop.Syntax
import Gaea.Logic.Prop.Notation

universes u w
variable {P : Sort u}

namespace Gaea.Logic

--------------------------------------------------------------------------------
-- Proof by Contraposition
-- (~q |- ~p) -> (|- p -> q)
--------------------------------------------------------------------------------

class ByContraposition (L : Logic P) (larr : Binar P) (lneg : Unar P) :=
  byContraposition : (p q : P) -> ((L |- ~q) -> (L |- ~p)) -> (L |- p -> q) 

abbrev byContraposition {L : Logic P} {larr lneg}
  [K : ByContraposition L larr lneg] {p q} := K.byContraposition p q

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

abbrev ModusTollens (L : Logic P) (larr : Binar P) (lneg : Unar P)
  := RightMt L larr lneg

abbrev mt {L : Logic P} {larr lneg} 
  [K : RightMt L larr lneg] {p q} := K.mt p q

--------------------------------------------------------------------------------
-- Modus Tollendo Ponens
--------------------------------------------------------------------------------

-- p \/ q, ~p |- q

class LeftMtp (L : Logic P) (disj : Binar P) (lneg : Unar P) := 
  mtp : (p q : P) -> (L |- p \/ q) -> (L |- ~p) -> (L |- q)

abbrev leftMtp {L : Logic P} {disj} {lneg : Unar P} 
  [K : LeftMtp L disj lneg] {p q} := K.mtp p q

abbrev ModusTollendoPonens (L : Logic P) (larr : Binar P) (lneg : Unar P)
  := LeftMtp L larr lneg

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