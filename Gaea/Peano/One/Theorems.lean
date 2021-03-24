import Gaea.Peano.Rules
import Gaea.Peano.Eq.Rules
import Gaea.Peano.One.Rules

universes u v

open Gaea.Math
open Gaea.Logic

namespace Gaea.Peano

instance iNatOneByNatEq
  {P : Sort u} {T : Type v} 
  {L : Logic P} [N : IsNat P T] [Q : LEq P T] [Z : Zero T] [O : One T] [Su : Succ T] 
  [NatEqNat L N Q] [NatZero L N Z] [NatSuccNat L N Su] [OneEqSuccZero L Q Z O Su] 
  : NatOne L N O := {natOne := natEq (natS nat0) oneEqSuccZero}

end Gaea.Peano
