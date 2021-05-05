import Gaea.Prelude.Newtype
import Gaea.Prelude.FunTypes
import Gaea.Logic.Judgment

universes u w
variable {P : Sort u}

namespace Gaea

--------------------------------------------------------------------------------
-- Contradiction
--------------------------------------------------------------------------------

def Contradiction (L : Logic P) (f : Unar P) :=
  PSigma fun (p : P) => L.Prod (f p) p 

def contradiction {L : Logic P} {f}
  {p} (LNp : L |- f p) (Lp : L |- p) : Contradiction L f := 
    PSigma.mk p (L.prod LNp Lp)

-- Proof by Contradiction
-- ((|- p) -> Contradiction) -> (|- f p)

class funtype ByContradiction (L : Logic P) (f : Unar P) := 
  {p : P} : ((L |- p) -> Contradiction L f) -> (L |- f p)

abbrev byContradiction {L : Logic P} {f}
  [K : ByContradiction L f] {p} := unpack K p

--------------------------------------------------------------------------------
-- Falsity
--------------------------------------------------------------------------------

-- Consistency
-- Not (|- p, ~p)

class funtype Noncontradiction (L : Logic P) (f : Unar P) := 
  {p : P} : (L |- f p) -> (L |- p) -> False

abbrev noncontradiction {L : Logic P} {f} 
  [K : Noncontradiction L f] {p} := unpack K p

-- Proof by Unprovability
-- ((|- p) -> False) -> (|- f p)

class funtype AdFalso (L : Logic P) (f : Unar P) := 
  {p : P} : ((L |- p) -> False) -> (L |- f p) 

abbrev adFalso {L : Logic P} {f}
  [K : AdFalso L f] {p} := unpack K p

instance iAdFalsoOfByContradicction 
{L : Logic P} {f} [K : ByContradiction L f] : AdFalso L f 
:= pack fun p Lpf => unpack K p (fun Lp => False.elim (Lpf Lp))

-- Argument to Falsity
-- (p |- falsum) -> (|- f p)

class funtype AdFalsum (L : Logic P) (falsum : P) (f : Unar P) := 
  {p : P} : ((L |- p) -> (L |- falsum)) -> (L |- f p)

abbrev adFalsum {L : Logic P} {falsum : P} {f : Unar P}
  [K : AdFalsum L falsum f] {p} := unpack K p

instance iAdFalsoOfAdFalsum
{L : Logic P} {falsum f} [K : AdFalsum L falsum f] : AdFalso L f 
:= pack fun p Lpf => unpack K p (fun Lp => False.elim (Lpf Lp))

-- Principle of Explosion
-- (|- falsum) -> (|- p)

class funtype ExFalsum (L : Logic P) (falsum : P) := 
  {p : P} : (L |- falsum) -> (L |- p)

abbrev exFalsum {L : Logic P} {falsum}
  [K : ExFalsum L falsum] {p} := unpack K p

--------------------------------------------------------------------------------
-- Proof by Contraposition
-- (~q |- ~p) -> (|- p -> q)
--------------------------------------------------------------------------------

class funtype ByContraposition (L : Logic P) (F : Binar P) (f : Unar P) := 
  {p q : P} : ((L |- f q) -> (L |- f p)) -> (L |- F p q) 

abbrev byContraposition {L : Logic P} {F f}
  [K : ByContraposition L F f] {p q} := unpack K p q

--------------------------------------------------------------------------------
-- Modus Tollens
--------------------------------------------------------------------------------

-- F p q, f p |- q 

class funtype LeftMt (L : Logic P) (F : Binar P) (f : Unar P) := 
  {p q : P} : (L |- F p q) -> (L |- f p) -> (L |- f q) 

abbrev leftMt {L : Logic P} {F f} 
  [K : LeftMt L F f] {p q} := unpack K p q

abbrev mtr {L : Logic P} {F f} 
  [K : LeftMt L F f] {p q} := unpack K p q

-- F p q, f q |- ~p 

class funtype RightMt (L : Logic P) (F : Binar P) (f : Unar P) := 
  {p q : P} : (L |- F p q) -> (L |- f q) -> (L |- f p)

abbrev rightMt {L : Logic P} {F f} 
  [K : RightMt L F f] {p q} := unpack K p q

abbrev ModusTollens (L : Logic P) (F : Binar P) (f : Unar P)
  := RightMt L F f

abbrev mt {L : Logic P} {F f} 
  [K : RightMt L F f] {p q} := unpack K p q

--------------------------------------------------------------------------------
-- Modus Tollendo Ponens
--------------------------------------------------------------------------------

-- F p q, f p |- q

class funtype LeftMtp (L : Logic P) (F : Binar P) (f : Unar P) := 
  {p q : P} : (L |- F p q) -> (L |- f p) -> (L |- q)

abbrev leftMtp {L : Logic P} {F} {f : Unar P} 
  [K : LeftMtp L F f] {p q} := unpack K p q

abbrev ModusTollendoPonens (L : Logic P) (F : Binar P) (f : Unar P)
  := LeftMtp L F f

abbrev mtp {L : Logic P} {F} {f : Unar P} 
  [K : LeftMtp L F f] {p q} := unpack K p q

-- F p q, f q |- p

class funtype RightMtp (L : Logic P) (F : Binar P) (f : Unar P) := 
  {p q : P} : (L |- F p q) -> (L |- f q) -> (L |- p)

abbrev rightMtp {L : Logic P} {F} {f : Unar P} 
  [K : RightMtp L F f] {p q} := unpack K p q

abbrev mtpr {L : Logic P} {F} {f : Unar P} 
  [K : RightMtp L F f] {p q} := unpack K p q

