import Logos.Peano.Nat
import Logos.Math.Syntax
import Logos.Logic.Judgment
import Logos.Logic.Eq.Syntax

universes u v
variable {P : Sort u} {T : Sort v}

open Logos.Notation
namespace Logos.Peano

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
