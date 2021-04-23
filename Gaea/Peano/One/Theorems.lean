import Gaea.Peano.Rules
import Gaea.Peano.Eq.Rules
import Gaea.Peano.One.Rules

universes u v

open Gaea.Math
open Gaea.Logic

namespace Gaea.Peano

instance iNatOneByNatEq
  {P : Sort u} {T : Sort v} 
  {L : Logic P} [N : IsNat P T] [Q : SEq P T] [Z : Zero T] [O : One T] [S : Succ T] 
  [NatEqNat L N Q] [NatZero L N Z] [NatSuccNat L N S] [OneEqSuccZero L Q Z O S] 
  : NatOne L N O := {toFun := natEq (natS nat0) oneEqSuccZero}

end Gaea.Peano
