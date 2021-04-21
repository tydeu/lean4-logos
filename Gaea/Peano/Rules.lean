import Gaea.Math.Notation
import Gaea.Logic.Judgment
import Gaea.Logic.Prop.Syntax
import Gaea.Logic.Prop.Notation
import Gaea.Logic.Eq.Syntax
import Gaea.Logic.Eq.Notation
import Gaea.Logic.Rel.Rules
import Gaea.Peano.Nat

universes u v
variable {P : Sort u} {T : Sort v}

open Gaea.Math
open Gaea.Logic

namespace Gaea.Peano

-- Axiom 1
class NatZero (L : Logic P) (N : IsNat P T) (Z : Zero T) :=
  natZero : L |- nat (0 : T)

abbrev natZero (L : Logic P) (T : Sort v) [N : IsNat P T] [Z : Zero T] 
  [K : NatZero L N Z] := K.natZero

abbrev nat0 {L : Logic P} [N : IsNat P T] [Z : Zero T] 
  [K : NatZero L N Z] := K.natZero

-- Axiom 6
class NatSuccNat (L : Logic P) (N : IsNat P T) (S : Succ T) :=
  natSuccNat : (n : T) -> (L |- nat n) -> (L |- nat (S n))

abbrev natSuccNat {L : Logic P} [N : IsNat P T] [S : Succ T] 
  [K : NatSuccNat L N S] {n} := K.natSuccNat n

abbrev natS {L : Logic P} [N : IsNat P T] [S : Succ T] 
  [K : NatSuccNat L N S] {n} := K.natSuccNat n

-- Axiom 7a
class EqNatToEqSucc (L : Logic P) (N : IsNat P T) (Q : SEq P T) (S : Succ T) :=
  eqNatToEqSucc : (m n : T) -> (L |- nat m) -> (L |- nat n) -> 
    (L |- m = n) -> (L |- S m = S n)

instance iEqNatToEqSuccOfFSubstT
  {L : Logic P} [N : IsNat P T] [Q : SEq P T] [S : Succ T]
  [K : EqNatToEqSucc L N Q S] : FSubstT L Q.toFun N.isNat S.toFun 
  := {fSubstT := K.eqNatToEqSucc}

instance iFSubstTOfEqNatToEqSucc
  {L : Logic P} [N : IsNat P T] [Q : SEq P T] [S : Succ T]
  [K : FSubstT L Q.toFun N.isNat S.toFun] : EqNatToEqSucc L N Q S
  := {eqNatToEqSucc := K.fSubstT}

abbrev eqNatToEqSucc {L : Logic P} [N : IsNat P T] [Q : SEq P T] [S : Succ T]
  [K : EqNatToEqSucc L N Q S] {m n} := K.eqNatToEqSucc m n

-- Axiom 7b
class EqSuccToEqNat (L : Logic P) (N : IsNat P T) (Q : SEq P T) (S : Succ T) :=
  eqSuccToEqNat : (m n : T) -> (L |- nat m) -> (L |- nat n) -> 
    (L |- S m = S n) -> (L |- m = n)

abbrev eqSuccToEqNat {L : Logic P} [N : IsNat P T] [Q : SEq P T] [S : Succ T]
  [K : EqSuccToEqNat L N Q S] {m n} := K.eqSuccToEqNat m n

-- Axiom 8
class SuccNatEqZeroFalse (L : Logic P) (N : PNat P T) (Q : SEq P T) :=
  succNatEqZeroFalse : (n : T) -> (L |- nat n) -> (L |- S n = 0) -> False

abbrev succNatEqZeroFalse {L : Logic P} [N : PNat P T] [Q : SEq P T]
  [K : SuccNatEqZeroFalse L N Q] {n} := K.succNatEqZeroFalse n

end Gaea.Peano
