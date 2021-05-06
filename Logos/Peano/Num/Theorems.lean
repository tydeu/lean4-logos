import Logos.Peano.Eq.Rules
import Logos.Peano.Num.Rules
import Logos.Peano.Succ.Rules

universes u v

namespace Logos.Peano

instance iNatOneByNatEq
  {P : Sort u} {T : Sort v} 
  {L : Logic P} [N : SNat P T] [Q : SEq P T] [Z : Zero T] [O : One T] [S : Succ T] 
  [NatEqNat L N Q] [NatZero L N Z] [NatSuccNat L N S] [OneEqSuccZero L Q Z O S] 
  : NatOne L N O := {toFun := natEq (natS nat0) oneEqSuccZero}
