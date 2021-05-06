import Logos.Peano.Eq
import Logos.Peano.Num
import Logos.Peano.Succ

universe v

open Logos.Notation
namespace Logos.Peano.Completeness

--------------------------------------------------------------------------------
-- Peano Prop
--------------------------------------------------------------------------------

inductive PProp (T : Sort v)
  | nat : T -> PProp T
  | eq : T -> T ->  PProp T

instance SEqOfPProp {T : Sort v} : SEq (PProp T) T 
  := pack PProp.eq
instance SNatOfPProp {T : Sort v} : SNat (PProp T) T 
  := pack PProp.nat

-- Logic type
def PLogic := Logic (PProp Nat)

--------------------------------------------------------------------------------
-- Nat Closure
--------------------------------------------------------------------------------

theorem natNat {L : PLogic}
[NZ : NatZero L SNatOfPProp Zero.ofNat]
[NS : NatSuccNat L SNatOfPProp Succ.ofNat]
: (n : Nat) -> (L |- nat n)
:= by
  intro n
  induction n with
  | zero => exact NZ.toFun
  | succ n Nn => exact NS.toFun n Nn 

--------------------------------------------------------------------------------
-- Meta Completeness
--------------------------------------------------------------------------------

theorem metaComplete (L : PLogic)
[NZ   : NatZero L SNatOfPProp Zero.ofNat]
[NS   : NatSuccNat L SNatOfPProp Succ.ofNat]
[QRf  : EqNatRefl L SNatOfPProp SEqOfPProp]
[QSm  : EqNatSymm L SNatOfPProp SEqOfPProp]
[QNtS : EqNatToEqSucc L SNatOfPProp SEqOfPProp Succ.ofNat]
[QStN : EqSuccToEqNat L SNatOfPProp SEqOfPProp Succ.ofNat]
[QS0f : SuccNatEqZeroFalse L SNatOfPProp SEqOfPProp Zero.ofNat Succ.ofNat]
: (p : PProp Nat) -> PSum (L |- p) (L !|- p)
:= by
  intro p
  cases p with
  | nat n =>
    apply PSum.inl
    exact natNat n
  | eq m n =>
    revert m
    induction n with
    | zero =>
      intro m
      induction m with
      | zero =>
        apply PSum.inl
        exact eqNatRefl NZ.toFun
      | succ m ih =>
        apply PSum.inr
        refine QS0f.toFun m (natNat m)
    | succ n n_ih =>
      intro m
      have Nn : L |- nat n := natNat n
      cases m with
      | zero =>
        apply PSum.inr
        intro Q0Sn
        apply QS0f.toFun n Nn 
        apply eqNatSymm (natNat Nat.zero) (natS Nn)
        exact Q0Sn
      | succ m =>
        have Nm : L |- nat m := natNat m
        cases n_ih m with
        | inl Qmn =>
          apply PSum.inl
          exact QNtS.toFun m n Nm Nn Qmn
        | inr Qmnf =>
          apply PSum.inr
          intro QSmSn
          apply Qmnf
          exact QStN.toFun m n Nm Nn QSmSn

--------------------------------------------------------------------------------
-- Meta Consistency
--------------------------------------------------------------------------------

theorem metaConsistent (L : PLogic)
[NZ   : NatZero L SNatOfPProp Zero.ofNat]
[NS   : NatSuccNat L SNatOfPProp Succ.ofNat]
[QRf  : EqNatRefl L SNatOfPProp SEqOfPProp]
[QSm  : EqNatSymm L SNatOfPProp SEqOfPProp]
[QNtS : EqNatToEqSucc L SNatOfPProp SEqOfPProp Succ.ofNat]
[QStN : EqSuccToEqNat L SNatOfPProp SEqOfPProp Succ.ofNat]
[QS0f : SuccNatEqZeroFalse L SNatOfPProp SEqOfPProp Zero.ofNat Succ.ofNat]
: (p : PProp Nat) -> PProd (L |- p) (L !|- p) -> False
:= by
  intro p
  cases p with
  | nat n =>
    intro C
    apply C.2
    exact natNat n
  | eq m n =>
    revert m
    induction n with
    | zero =>
      intro m C
      induction m with
      | zero =>
        apply C.2
        exact eqNatRefl NZ.toFun
      | succ m ih =>
        exact QS0f.toFun m (natNat m) C.1
    | succ n n_ih =>
      intro m C
      have Nn : L |- nat n := natNat n
      cases m with
      | zero =>
        apply QS0f.toFun n Nn 
        apply eqNatSymm (natNat Nat.zero) (natS Nn)
        exact C.1
      | succ m =>
        have Nm : L |- nat m := natNat m
        apply n_ih m
        apply PProd.mk ?Qmn ?Qmnf
        case Qmn =>
          exact QStN.toFun m n Nm Nn C.1
        case Qmnf =>
          intro Qmn
          apply C.2
          exact QNtS.toFun m n Nm Nn Qmn
