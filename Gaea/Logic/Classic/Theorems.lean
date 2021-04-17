import Gaea.Logic.Prop.Rules
import Gaea.Logic.Prop.Tactics
import Gaea.Logic.Classic.Rules

namespace Gaea.Logic

universe u
variable {P : Sort u}

--------------------------------------------------------------------------------
-- Dilemmas
--------------------------------------------------------------------------------

-- Constructive Dilemma
-- (p -> q) /\ (r -> s) /\ (p \/ r) |- q \/ s 

def cnstrDilByUncurryMpDisj {L : Logic P} 
{larr : Binar P} {conj : Binar P} {disj : Binar P}
(CjU : Uncurry L conj) 
(Mp  : ModusPonens L larr) 
(DiL : LeftTaut L disj)
(DiR : RightTaut L disj) 
(DjE : ByEither L disj)
: (p q r s : P) -> 
    (L |- (p -> q) /\ (r -> s) /\ (p \/ r)) -> (L |- q \/ s) 
:= by
  intro p q r s
  assume (LpTq, LrTs, LpDr)
  byEither LpDr ?pTqDs ?rTqDs
  case pTqDs =>
    intro Lp
    apply leftTaut
    mp LpTq Lp
  case rTqDs =>
    intro Lr
    apply rightTaut
    mp LrTs Lr

instance iCnstrDilByUncurryMpDisj {L : Logic P} 
{larr : Binar P} {conj : Binar P} {disj : Binar P}
[Mp  : ModusPonens L larr]
[CjU : Uncurry L conj]
[DiL : LeftTaut L disj]
[DiR : RightTaut L disj] 
[DjE : ByEither L disj]
: CnstrDil L larr conj disj :=
{cnstrDil := cnstrDilByUncurryMpDisj CjU Mp DiL DiR DjE} 

-- Destructive Dilemma
-- (p -> q) /\ (r -> s) /\ (~q \/ ~s) |- ~p \/ ~r 

def destrDilByUncurryMtDisj {L : Logic P} 
{larr : Binar P} {conj : Binar P} {disj : Binar P} {lneg : Unar P}
(CjU : Uncurry L conj) 
(Mt : ModusTollens L larr lneg)
(DiL : LeftTaut L disj)
(DiR : RightTaut L disj) 
(DjE : ByEither L disj)
: (p q r s : P) -> 
    (L |- (p -> q) /\ (r -> s) /\ (~q \/ ~s)) -> (L |- ~p \/ ~r) 
:= by
  intro p q r s
  assume (LpTq, LrTs, LNqDNs)
  byEither LNqDNs ?NqTNpDNr ?NsTNpDNr
  case NqTNpDNr =>
    intro LNq
    apply leftTaut
    mt LpTq LNq
  case NsTNpDNr =>
    intro LNs
    apply rightTaut
    mt LrTs LNs

instance iDestrDilByUncurryMtDisj {L : Logic P} 
{larr : Binar P} {conj : Binar P} {disj : Binar P} {lneg : Unar P}
[CjU : Uncurry L conj]
[Mt : ModusTollens L larr lneg]
[DiL : LeftTaut L disj]
[DiR : RightTaut L disj] 
[DjE : ByEither L disj]
: DestrDil L larr conj disj lneg :=
{destrDil := destrDilByUncurryMtDisj CjU Mt DiL DiR DjE } 

-- Bidirectional Dilemma
-- (p -> q) /\ (r -> s) /\ (p \/ ~s) |- q \/ ~r 

def bidirDilByUncurryMpMtDisj {L : Logic P} 
{larr : Binar P} {conj : Binar P} {disj : Binar P} {lneg : Unar P}
(CjU : Uncurry L conj)
(Mp  : ModusPonens L larr) 
(Mt  : ModusTollens L larr lneg)
(DiL : LeftTaut L disj)
(DiR : RightTaut L disj) 
(DjE : ByEither L disj)
: (p q r s : P) -> 
    (L |- (p -> q) /\ (r -> s) /\ (p \/ ~s)) -> (L |- q \/ ~r) 
:= by
  intro p q r s
  assume (LpTq, LrTs, LpDNs)
  byEither LpDNs ?pTqDNr ?NsTqDNr
  case pTqDNr =>
    intro Lp
    apply leftTaut
    mp LpTq Lp
  case NsTqDNr =>
    intro LNs
    apply rightTaut
    mt LrTs LNs

instance iBidirDilByUncurryMpMtDisj {L : Logic P} 
{larr : Binar P} {conj : Binar P} {disj : Binar P} {lneg : Unar P}
[Mp  : ModusPonens L larr]
[Mt  : ModusTollens L larr lneg]
[CjU : Uncurry L conj]
[DiL : LeftTaut L disj]
[DiR : RightTaut L disj] 
[DjE : ByEither L disj]
: BidirDil L larr conj disj lneg :=
{bidirDil := bidirDilByUncurryMpMtDisj CjU Mp Mt DiL DiR DjE} 

end Gaea.Logic
