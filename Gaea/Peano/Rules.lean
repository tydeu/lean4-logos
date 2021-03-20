import Gaea.Math.Notation
import Gaea.Logic.Notation
import Gaea.Logic.Eq.Rules
import Gaea.Peano.Nat

universes u v w

open Gaea.Math
open Gaea.Logic

namespace Gaea.Peano

-- Axiom 1
class NatZero {P : Sort u} {T : Type v} 
  (L : Logic P) (N : IsNat P T) (Z : Zero T) :=
  (natZero : L |- nat (0 : T))

def natZero {P : Sort u} (L : Logic P) (T : Type v) 
  [N : IsNat P T] [Z : Zero T] [K : NatZero L N Z] := K.natZero

def nat0 {P : Sort u} {T : Type v} 
  {L : Logic P} [N : IsNat P T] [Z : Zero T] [K : NatZero L N Z] := K.natZero

-- Axiom 6
class NatSuccNat {P : Sort u} {T : Sort v} 
  (L : Logic P) (N : IsNat P T) (NS : Succ T) :=
  (natSuccNat : (n : T) -> (L |- nat n) -> (L |- nat (S n)))

def natSuccNat {P : Sort u} {T : Sort v} 
{L : Logic P} [N : IsNat P T] [NS : Succ T] [K : NatSuccNat L N NS] 
{n : T} := K.natSuccNat n

def natS {P : Sort u} {T : Sort v} 
{L : Logic P} [N : IsNat P T] [NS : Succ T] [K : NatSuccNat L N NS] 
{n : T} := K.natSuccNat n

-- Axiom 7a
class EqNatToEqSucc {P : Sort u} {T : Sort v} 
  (L : Logic P) (N : IsNat P T) (Q : LEq P T) (NS : Succ T) :=
  (eqNatToEqSucc : (m n : T) -> (L |- nat m) -> (L |- nat n) -> 
    (L |- m = n) -> (L |- S m = S n))

instance {P : Sort u} {T : Type v} 
  {L : Logic P} [N : IsNat P T] [Q : LEq P T] [NS : Succ T]
  [K : EqNatToEqSucc L N Q NS] : EqMemToEqFun L Q N.isNat NS.succ 
  := {eqMemToEqFun := K.eqNatToEqSucc}

instance {P : Sort u} {T : Type v} 
  {L : Logic P} [N : IsNat P T] [Q : LEq P T] [NS : Succ T]
  [K : EqMemToEqFun L Q N.isNat NS.succ] : EqNatToEqSucc L N Q NS
  := {eqNatToEqSucc := K.eqMemToEqFun}

def eqNatToEqSucc {P : Sort u} {T : Sort v} 
  {L : Logic P} [N : IsNat P T] [Q : LEq P T] [NS : Succ T]
  [K : EqNatToEqSucc L N Q NS] {m n : T} := K.eqNatToEqSucc m n

-- Axiom 7b
class EqSuccToEqNat {P : Sort u} {T : Sort v} 
  (L : Logic P) (N : IsNat P T) (Q : LEq P T) (NS : Succ T) :=
  (eqSuccToEqNat : (m n : T) -> (L |- nat m) -> (L |- nat n) -> 
    (L |- S m = S n) -> (L |- m = n))

def eqSuccToEqNat {P : Sort u} {T : Sort v} 
  {L : Logic P} [N : IsNat P T] [Q : LEq P T] [NS : Succ T]
  [K : EqSuccToEqNat L N Q NS] {m n : T} := K.eqSuccToEqNat

-- Axiom 8
class SuccNatEqZeroFalse {P : Sort u} {T : Type v} 
  (L : Logic P) (N : PNat P T) (Q : LEq P T) (F : LFalse P) :=
  (succNatEqZeroFalse : (m n : T) -> (L |- nat m) -> (L |- nat n) -> 
    (L |- S n = 0) -> (L |- false))

def succNatEqZeroFalse {P : Sort u} {T : Type v} 
  {L : Logic P} [N : PNat P T] [Q : LEq P T] [F : LFalse P]
  [K : SuccNatEqZeroFalse L N Q F] {m n : T} := K.succNatEqZeroFalse m n

end Gaea.Peano
