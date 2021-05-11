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
: (p : PProp Nat) -> Sum (L |- p) (L !|- p)
:= by
  intro p
  cases p with
  | nat n =>
    apply Sum.inl
    exact natNat n
  | eq m n =>
    revert m
    induction n with
    | zero =>
      intro m
      induction m with
      | zero =>
        apply Sum.inl
        exact eqNatRefl NZ.toFun
      | succ m ih =>
        apply Sum.inr
        apply noJudgment 
        exact QS0f.toFun m (natNat m)
    | succ n n_ih =>
      intro m
      have Nn : L |- nat n := natNat n
      cases m with
      | zero =>
        apply Sum.inr
        apply noJudgment
        intro Q0Sn
        apply QS0f.toFun n Nn 
        apply eqNatSymm (natNat Nat.zero) (natS Nn)
        exact Q0Sn
      | succ m =>
        have Nm : L |- nat m := natNat m
        cases n_ih m with
        | inl Qmn =>
          apply Sum.inl
          exact QNtS.toFun m n Nm Nn Qmn
        | inr Qmnf =>
          apply Sum.inr
          apply noJudgment
          intro QSmSn
          apply Qmnf.proof
          exact QStN.toFun m n Nm Nn QSmSn
