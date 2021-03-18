import Gaea.Peano.Nat
import Gaea.Logic.Eq.Rules

universes u v w

open Gaea.Logic
open Gaea.Syntax

namespace Gaea.Peano

--------------------------------------------------------------------------------
-- Transitivity w/ Implied Nats
--------------------------------------------------------------------------------

-- (a = b) /\ (b = c) -> (a = c)

class EqTransNat {P : Sort u} {T : Type v} 
  (L : Logic P) (N : IsNat P T) (Q : LEq P T) :=
  (eqTransNat : (a b c : T) -> 
    (L |- nat c) -> (L |- a = b) -> (L |- b = c) -> (L |- a = c))

def eqTransNat {P : Sort u} {T : Type v} 
{L : Logic P} [N : IsNat P T] [Q : LEq P T] [K : EqTransNat L N Q]
{a : T} (b : T) {c : T} := K.eqTransNat a b c

def eqTransNat' {P : Sort u} {T : Type v} 
{L : Logic P} [N : IsNat P T] [Q : LEq P T] [K : EqTransNat L N Q]
{a b c : T} := K.eqTransNat a b c

--------------------------------------------------------------------------------
-- Euclideaness
--------------------------------------------------------------------------------

-- Left Euclidean
-- (b = a) /\ (c = a) -> (b = c)

class EqNatLeftEuc {P : Sort u} {T : Type v} 
  (L : Logic P) (N : IsNat P T) (Q : LEq P T) :=
  (eqNatLeftEuc : (a b c : T) -> 
    (L |- nat a) -> (L |- nat b) -> (L |- nat c) -> 
    (L |- b = a) -> (L |- c = a) -> (L |- b = c))

instance {P : Sort u} {T : Type v} 
  (L : Logic P) [N : IsNat P T] [Q : LEq P T] [K : EqNatLeftEuc L N Q] 
  : EqMemLeftEuc L Q N.isNat := {eqMemLeftEuc := K.eqNatLeftEuc}

instance {P : Sort u} {T : Type v} 
  (L : Logic P) [N : IsNat P T] [Q : LEq P T] [K : EqMemLeftEuc L Q N.isNat] 
  : EqNatLeftEuc L N Q := {eqNatLeftEuc := K.eqMemLeftEuc}

def eqNatLeftEuc {P : Sort u} {T : Type v} 
  {L : Logic P} [N : IsNat P T] [Q : LEq P T]
  [C : EqNatLeftEuc L N Q] {a b c : T} := C.eqNatLeftEuc a b c 

-- w/ Implied Nats
class EqLeftEucNat {P : Sort u} {T : Type v} 
  (L : Logic P) (N : IsNat P T) (Q : LEq P T) :=
  (eqLeftEucNat : (a b c : T) -> (L |- nat a) -> 
    (L |- b = a) -> (L |- c = a) -> (L |- b = c))

def eqLeftEucNat {P : Sort u} {T : Type v} 
  {L : Logic P} [N : IsNat P T] [Q : LEq P T]
  [C : EqLeftEucNat L N Q] {a b c : T} := C.eqLeftEucNat a b c 

-- Right Euclidean
-- (a = b) /\ (a = c) -> (b = c)

class EqNatRightEuc {P : Sort u} {T : Type v} 
  (L : Logic P) (N : IsNat P T) (Q : LEq P T) :=
  (eqNatRightEuc : (a b c : T) -> 
    (L |- nat a) -> (L |- nat b) -> (L |- nat c) -> 
    (L |- a = b) -> (L |- a = c) -> (L |- b = c))

instance {P : Sort u} {T : Type v} 
  (L : Logic P) [N : IsNat P T] [Q : LEq P T] [K : EqNatRightEuc L N Q] 
  : EqMemRightEuc L Q N.isNat := {eqMemRightEuc := K.eqNatRightEuc}

instance {P : Sort u} {T : Type v} 
  (L : Logic P) [N : IsNat P T] [Q : LEq P T] [K : EqMemRightEuc L Q N.isNat] 
  : EqNatRightEuc L N Q := {eqNatRightEuc := K.eqMemRightEuc}

def eqNatRightEuc {P : Sort u} {T : Type v} 
  {L : Logic P} [N : IsNat P T] [Q : LEq P T]
  [C : EqNatLeftEuc L N Q] {a b c : T} := C.eqNatLeftEuc a b c 

end Gaea.Peano