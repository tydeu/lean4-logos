import Logos.Peano.Rules
import Logos.Peano.Eq.Rules
import Logos.Peano.Eq.Theorems

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
  := {toFun := PProp.eq}
instance IsNatOfPProp {T : Sort v} : IsNat (PProp T) T 
  := {isNat := PProp.nat}

instance PNatOfPPropNat : PNat (PProp Nat) Nat 
  := {toIsNat := IsNatOfPProp, toZero := inferInstance, toSucc := inferInstance}

-- Logic type
def PLogic := Logic (PProp Nat)

--------------------------------------------------------------------------------
-- Nat Closure
--------------------------------------------------------------------------------

theorem natNat {L : PLogic}
[NZ : NatZero L IsNatOfPProp Zero.ofNat]
[NS : NatSuccNat L IsNatOfPProp Succ.ofNat]
: (n : Nat) -> (L |- nat n)
:= by
  intro n
  induction n with
  | zero => exact NZ.toFun
  | succ n Nn => exact NS.toFun n Nn 

--------------------------------------------------------------------------------
-- Completeness
--------------------------------------------------------------------------------

theorem complete (L : PLogic)
[NZ   : NatZero L IsNatOfPProp Zero.ofNat]
[NS   : NatSuccNat L IsNatOfPProp Succ.ofNat]
[QRf  : EqNatRefl L IsNatOfPProp SEqOfPProp]
[QSm  : EqNatSymm L IsNatOfPProp SEqOfPProp]
[QNtS : EqNatToEqSucc L IsNatOfPProp SEqOfPProp Succ.ofNat]
[QStN : EqSuccToEqNat L IsNatOfPProp SEqOfPProp Succ.ofNat]
[QS0f : SuccNatEqZeroFalse L PNatOfPPropNat SEqOfPProp]
: (p : PProp Nat) -> (L |- p) \/ ((L |- p) -> False)
:= by
  intro p
  cases p with
  | nat n =>
    apply Or.inl
    exact natNat n
  | eq m n =>
    revert m
    induction n with
    | zero =>
      intro m
      induction m with
      | zero =>
        apply Or.inl
        exact eqNatRefl NZ.toFun
      | succ m ih =>
        apply Or.inr
        refine QS0f.toFun m (natNat m)
    | succ n n_ih =>
      intro m
      have Nn : L |- nat n := natNat n
      cases m with
      | zero =>
        apply Or.inr
        intro Q0Sn
        apply QS0f.toFun n Nn 
        apply eqNatSymm (natNat Nat.zero) (natS Nn)
        exact Q0Sn
      | succ m =>
        have Nm : L |- nat m := natNat m
        cases n_ih m with
        | inl Qmn =>
          apply Or.inl
          exact QNtS.toFun m n Nm Nn Qmn
        | inr Qmnf =>
          apply Or.inr
          intro QSmSn
          apply Qmnf
          exact QStN.toFun m n Nm Nn QSmSn

--------------------------------------------------------------------------------
-- Consistency
--------------------------------------------------------------------------------

theorem consistent (L : PLogic)
[NZ   : NatZero L IsNatOfPProp Zero.ofNat]
[NS   : NatSuccNat L IsNatOfPProp Succ.ofNat]
[QRf  : EqNatRefl L IsNatOfPProp SEqOfPProp]
[QSm  : EqNatSymm L IsNatOfPProp SEqOfPProp]
[QNtS : EqNatToEqSucc L IsNatOfPProp SEqOfPProp Succ.ofNat]
[QStN : EqSuccToEqNat L IsNatOfPProp SEqOfPProp Succ.ofNat]
[QS0f : SuccNatEqZeroFalse L PNatOfPPropNat SEqOfPProp]
: (p : PProp Nat) -> ((L |- p) /\ ((L |- p) -> False)) -> False
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
        apply And.intro ?Qmn ?Qmnf
        case Qmn =>
          exact QStN.toFun m n Nm Nn C.1
        case Qmnf =>
          intro Qmn
          apply C.2
          exact QNtS.toFun m n Nm Nn Qmn
