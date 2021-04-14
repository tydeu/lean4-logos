import Gaea.Peano.Nat
import Gaea.Math.Notation
import Gaea.Logic.Judgment
import Gaea.Logic.Eq.Syntax
import Gaea.Logic.Eq.Notation

universes u v

open Gaea.Math
open Gaea.Logic

namespace Gaea.Peano

class NatOne {P : Sort u} {T : Type v}
  (L : Logic P) (N : IsNat P T) (O : One T) :=
  (natOne : L |- nat (1 : T))

def natOne {P : Sort u} (L : Logic P) (T : Type v)  
   [N : IsNat P T] [O : One T] [K : NatOne L N O] 
  := K.natOne

def nat1 {P : Sort u} {T : Type v} 
  {L : Logic P} [N : IsNat P T] [O : One T] [K : NatOne L N O] 
  := K.natOne

class OneEqSuccZero {P : Sort u} {T : Type v} 
  (L : Logic P) (Q : SEq P T) (Z : Zero T) (O : One T) (Su : Succ T) :=
  (oneEqSuccZero : L |- (1 : T) = S (0 : T))

def oneEqSuccZero {P : Sort u} {T : Type v} 
  {L : Logic P} [Q : SEq P T] [Z : Zero T] [O : One T] [Su : Succ T]
  [K : OneEqSuccZero L Q Z O Su] := K.oneEqSuccZero

end Gaea.Peano
