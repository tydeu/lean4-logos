import Gaea.Peano.Nat
import Gaea.Math.Notation
import Gaea.Logic.Judgment
import Gaea.Logic.Eq.Syntax

universes u v
variable {P : Sort u} {T : Sort v}

open Gaea.Math
open Gaea.Logic
open Gaea.Logic.Notation

namespace Gaea.Peano

class NatOne (L : Logic P) (N : IsNat P T) (O : One T) :=
  toFun : L |- nat (1 : T)

abbrev natOne (L : Logic P) (T : Sort v) [N : IsNat P T] [O : One T] 
  [K : NatOne L N O] := K.toFun

abbrev nat1 {L : Logic P} {T : Sort v} [N : IsNat P T] [O : One T] 
  [K : NatOne L N O]  := K.toFun

class OneEqSuccZero (L : Logic P) 
  (Q : SEq P T) (Z : Zero T) (O : One T) (S : Succ T) :=
  toFun : L |- (1 : T) = S (0 : T)

abbrev oneEqSuccZero {L : Logic P} 
  [Q : SEq P T] [Z : Zero T] [O : One T] [S : Succ T]
  [K : OneEqSuccZero L Q Z O S] := K.toFun

end Gaea.Peano
