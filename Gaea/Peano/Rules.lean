import Gaea.Math.Notation
import Gaea.Logic.Judgment
import Gaea.Logic.Prop.Syntax
import Gaea.Logic.Eq.Syntax
import Gaea.Logic.Rel.Rules
import Gaea.Peano.Nat

universes u v
variable {P : Sort u} {T : Sort v}

open Gaea.Math
open Gaea.Logic
open Gaea.Logic.Notation

namespace Gaea.Peano

-- Axiom 1
class NatZero (L : Logic P) (N : IsNat P T) (Z : Zero T) :=
  toFun : L |- nat (0 : T)

abbrev natZero (L : Logic P) (T : Sort v) [N : IsNat P T] [Z : Zero T] 
  [K : NatZero L N Z] := K.toFun

abbrev nat0 {L : Logic P} [N : IsNat P T] [Z : Zero T] 
  [K : NatZero L N Z] := K.toFun

-- Axiom 6
class NatSuccNat (L : Logic P) (N : IsNat P T) (S : Succ T) :=
  toFun : (n : T) -> (L |- nat n) -> (L |- nat (S n))

abbrev natSuccNat {L : Logic P} [N : IsNat P T] [S : Succ T] 
  [K : NatSuccNat L N S] {n} := K.toFun n

abbrev natS {L : Logic P} [N : IsNat P T] [S : Succ T] 
  [K : NatSuccNat L N S] {n} := K.toFun n

-- Axiom 7a
class EqNatToEqSucc (L : Logic P) (N : IsNat P T) (Q : SEq P T) (S : Succ T) :=
  toFun : (m n : T) -> (L |- nat m) -> (L |- nat n) -> 
    (L |- m = n) -> (L |- S m = S n)

instance iEqNatToEqSuccOfFSubstT
  {L : Logic P} [N : IsNat P T] [Q : SEq P T] [S : Succ T]
  [K : EqNatToEqSucc L N Q S] : FSubstT L Q.toFun N.isNat S.toFun 
  := {toFun := K.toFun}

instance iFSubstTOfEqNatToEqSucc
  {L : Logic P} [N : IsNat P T] [Q : SEq P T] [S : Succ T]
  [K : FSubstT L Q.toFun N.isNat S.toFun] : EqNatToEqSucc L N Q S
  := {toFun := K.toFun}

abbrev eqNatToEqSucc {L : Logic P} [N : IsNat P T] [Q : SEq P T] [S : Succ T]
  [K : EqNatToEqSucc L N Q S] {m n} := K.toFun m n

-- Axiom 7b
class EqSuccToEqNat (L : Logic P) (N : IsNat P T) (Q : SEq P T) (S : Succ T) :=
  toFun : (m n : T) -> (L |- nat m) -> (L |- nat n) -> 
    (L |- S m = S n) -> (L |- m = n)

abbrev eqSuccToEqNat {L : Logic P} [N : IsNat P T] [Q : SEq P T] [S : Succ T]
  [K : EqSuccToEqNat L N Q S] {m n} := K.toFun m n

-- Axiom 8
class SuccNatEqZeroFalse (L : Logic P) (N : PNat P T) (Q : SEq P T) :=
  toFun : (n : T) -> (L |- nat n) -> (L |- S n = 0) -> False

abbrev succNatEqZeroFalse {L : Logic P} [N : PNat P T] [Q : SEq P T]
  [K : SuccNatEqZeroFalse L N Q] {n} := K.toFun n
