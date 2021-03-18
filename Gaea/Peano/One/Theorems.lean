import Gaea.Peano.Rules
import Gaea.Peano.One.Rules

universes u v

open Gaea.Logic
open Gaea.Syntax

namespace Gaea.Peano

instance natOne_inst
  {P : Sort u} {T : Type v} 
  {L : Logic P} [N : IsNat P T] [Q : LEq P T] [Z : Zero T] [O : One T] [Su : Succ T] 
  [NatEqNat L N Q] [NatZero L N Z] [NatSuccNat L N Su] [OneEqSuccZero L Q Z O Su] 
  : NatOne L N O := {natOne := natEq (natS nat0) oneEqSuccZero}

end Gaea.Peano