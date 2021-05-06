import Logos.Peano.Nat
import Logos.Prelude.NatLit
import Logos.Logic.Judgment
import Logos.Logic.Eq.Syntax

universes u v
variable {P : Sort u} {T : Sort v}

open Logos.Notation
namespace Logos.Peano

--------------------------------------------------------------------------------
-- Zero
--------------------------------------------------------------------------------

-- Axiom 1
class NatZero (L : Logic P) (N : SNat P T) (Z : Zero T) :=
  toFun : L |- nat (0 : T)

abbrev natZero (L : Logic P) (T : Sort v) [N : SNat P T] [Z : Zero T] 
  [K : NatZero L N Z] := K.toFun

abbrev nat0 {L : Logic P} [N : SNat P T] [Z : Zero T] 
  [K : NatZero L N Z] := K.toFun

--------------------------------------------------------------------------------
-- One
--------------------------------------------------------------------------------

-- Mem
class NatOne (L : Logic P) (N : SNat P T) (O : One T) :=
  toFun : L |- nat (1 : T)

abbrev natOne (L : Logic P) (T : Sort v) [N : SNat P T] [O : One T] 
  [K : NatOne L N O] := K.toFun

abbrev nat1 {L : Logic P} {T : Sort v} [N : SNat P T] [O : One T] 
  [K : NatOne L N O]  := K.toFun

-- Def
class OneEqSuccZero (L : Logic P) 
  (Q : SEq P T) (Z : Zero T) (O : One T) (S : Succ T) :=
  toFun : L |- (1 : T) = S (0 : T)

abbrev oneEqSuccZero {L : Logic P} 
  [Q : SEq P T] [Z : Zero T] [O : One T] [S : Succ T]
  [K : OneEqSuccZero L Q Z O S] := K.toFun
