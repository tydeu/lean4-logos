import Gaea.Math.Notation
import Gaea.Logic.Judgment
import Gaea.Logic.Prop.Syntax
import Gaea.Logic.Prop.Notation
import Gaea.Logic.Eq.Syntax
import Gaea.Logic.Eq.Notation
import Gaea.Logic.Rel.Rules
import Gaea.Peano.Nat

universes u v w

open Gaea.Math
open Gaea.Logic

namespace Gaea.Peano

-- Axiom 1
class NatZero {P : Sort u} {T : Sort v} 
  (L : Logic P) (N : IsNat P T) (Z : Zero T) :=
  (natZero : L |- nat (0 : T))

def natZero {P : Sort u} (L : Logic P) (T : Sort v) 
  [N : IsNat P T] [Z : Zero T] [K : NatZero L N Z] := K.natZero

def nat0 {P : Sort u} {T : Sort v} 
  {L : Logic P} [N : IsNat P T] [Z : Zero T] [K : NatZero L N Z] := K.natZero

-- Axiom 6
class NatSuccNat {P : Sort u} {T : Sort v} 
  (L : Logic P) (N : IsNat P T) (S : Succ T) :=
  (natSuccNat : (n : T) -> (L |- nat n) -> (L |- nat (S n)))

def natSuccNat {P : Sort u} {T : Sort v} 
{L : Logic P} [N : IsNat P T] [S : Succ T] [K : NatSuccNat L N S] 
{n : T} := K.natSuccNat n

def natS {P : Sort u} {T : Sort v} 
{L : Logic P} [N : IsNat P T] [S : Succ T] [K : NatSuccNat L N S] 
{n : T} := K.natSuccNat n

-- Axiom 7a
class EqNatToEqSucc {P : Sort u} {T : Sort v} 
  (L : Logic P) (N : IsNat P T) (Q : SEq P T) (S : Succ T) :=
  (eqNatToEqSucc : (m n : T) -> (L |- nat m) -> (L |- nat n) -> 
    (L |- m = n) -> (L |- S m = S n))

instance iEqNatToEqSuccOfFSubstT {P : Sort u} {T : Sort v} 
  {L : Logic P} [N : IsNat P T] [Q : SEq P T] [S : Succ T]
  [K : EqNatToEqSucc L N Q S] : FSubstT L Q.toFun N.isNat S.toFun 
  := {fSubstT := K.eqNatToEqSucc}

instance iFSubstTOfEqNatToEqSucc {P : Sort u} {T : Sort v} 
  {L : Logic P} [N : IsNat P T] [Q : SEq P T] [S : Succ T]
  [K : FSubstT L Q.toFun N.isNat S.toFun] : EqNatToEqSucc L N Q S
  := {eqNatToEqSucc := K.fSubstT}

def eqNatToEqSucc {P : Sort u} {T : Sort v} 
  {L : Logic P} [N : IsNat P T] [Q : SEq P T] [S : Succ T]
  [K : EqNatToEqSucc L N Q S] {m n : T} := K.eqNatToEqSucc m n

-- Axiom 7b
class EqSuccToEqNat {P : Sort u} {T : Sort v} 
  (L : Logic P) (N : IsNat P T) (Q : SEq P T) (S : Succ T) :=
  (eqSuccToEqNat : (m n : T) -> (L |- nat m) -> (L |- nat n) -> 
    (L |- S m = S n) -> (L |- m = n))

def eqSuccToEqNat {P : Sort u} {T : Sort v} 
  {L : Logic P} [N : IsNat P T] [Q : SEq P T] [S : Succ T]
  [K : EqSuccToEqNat L N Q S] {m n : T} := K.eqSuccToEqNat

-- Axiom 8
class SuccNatEqZeroFalse {P : Sort u} {T : Sort v} 
  (L : Logic P) (N : PNat P T) (Q : SEq P T) (F : LFalse P) :=
  (succNatEqZeroFalse : (m n : T) -> (L |- nat m) -> (L |- nat n) -> 
    (L |- S n = 0) -> (L |- false))

def succNatEqZeroFalse {P : Sort u} {T : Sort v} 
  {L : Logic P} [N : PNat P T] [Q : SEq P T] [F : LFalse P]
  [K : SuccNatEqZeroFalse L N Q F] {m n : T} := K.succNatEqZeroFalse m n

end Gaea.Peano
