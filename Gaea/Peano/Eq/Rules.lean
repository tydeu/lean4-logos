import Gaea.Peano.Nat
import Gaea.Logic.Eq.Rules

universes u v w

open Gaea.Logic

namespace Gaea.Peano

--------------------------------------------------------------------------------
-- Closure
--------------------------------------------------------------------------------

-- Axiom N5
class NatEqNat {P : Sort u} {T : Sort v} 
  (L : Logic P) (N : IsNat P T) (Q : LEq P T) :=
  (natEqNat : (a b : T) -> (L |- nat b) -> (L |- a = b) -> (L |- nat a))

def natEqNat {P : Sort u} {T : Sort v} 
  {L : Logic P} [N : IsNat P T] [Q : LEq P T] [K : NatEqNat L N Q] 
  {a b : T} := K.natEqNat a b

def natEq {P : Sort u} {T : Sort v} 
  {L : Logic P} [N : IsNat P T] [Q : LEq P T] [K : NatEqNat L N Q] 
  {a b : T} := K.natEqNat a b

--------------------------------------------------------------------------------
-- Reflexivity
-- a -> (a = a)
--------------------------------------------------------------------------------

-- Axiom N2
class EqNatRefl {P : Sort u} {T : Sort v} 
  (L : Logic P) (N : IsNat P T) (Q : LEq P T) :=
  (eqNatRefl : (x : T) -> (L |- nat x) -> (L |- x = x))

instance {P : Sort u} {T : Type v} 
  {L : Logic P} [N : IsNat P T] [Q : LEq P T]
  [K : EqNatRefl L N Q] : EqMemRefl L Q N.isNat 
  := {eqMemRefl := K.eqNatRefl}

instance {P : Sort u} {T : Type v} 
  {L : Logic P} [N : IsNat P T] [Q : LEq P T] [A : Add T] 
  [K : EqMemRefl L Q N.isNat] : EqNatRefl L N Q
  := {eqNatRefl := K.eqMemRefl}

def eqNatRefl {P : Sort u} {T : Sort v} 
  {L : Logic P} [N : IsNat P T] [Q : LEq P T] [K : EqNatRefl L N Q]
  {x : T} := K.eqNatRefl x

--------------------------------------------------------------------------------
-- Symmetry
-- (a = b) /\ (b = c) -> (a = c)
--------------------------------------------------------------------------------

-- Axiom N3
class EqNatSymm {P : Sort u} {T : Sort v} 
  (L : Logic P) (N : IsNat P T) (Q : LEq P T) :=
  (eqNatSymm : (x y : T) -> (L |- nat x) -> (L |- nat y) ->
    (L |- x = y) -> (L |- y = x))

instance {P : Sort u} {T : Type v} 
  {L : Logic P} [N : IsNat P T] [Q : LEq P T]
  [K : EqNatSymm L N Q] : EqMemSymm L Q N.isNat 
  := {eqMemSymm := K.eqNatSymm}

instance {P : Sort u} {T : Type v} 
  {L : Logic P} [N : IsNat P T] [Q : LEq P T] [A : Add T] 
  [K : EqMemSymm L Q N.isNat] : EqNatSymm L N Q
  := {eqNatSymm := K.eqMemSymm}

def eqNatSymm {P : Sort u} {T : Sort v} 
  {L : Logic P} [N : IsNat P T] [Q : LEq P T] [K : EqNatSymm L N Q]
  {x y : T} := K.eqNatSymm x y

--------------------------------------------------------------------------------
-- Transitivity
-- (a = b) /\ (b = c) -> (a = c)
--------------------------------------------------------------------------------

-- Axiom N4
class EqNatTrans {P : Sort u} {T : Sort v} 
  (L : Logic P) (N : IsNat P T) (Q : LEq P T) :=
  (eqNatTrans : (x y z : T) -> (L |- nat x) -> (L |- nat y) -> (L |- nat z) -> 
    (L |- x = y) -> (L |- y = z) -> (L |- x = z))

instance {P : Sort u} {T : Type v} 
  {L : Logic P} [N : IsNat P T] [Q : LEq P T]
  [K : EqNatTrans L N Q] : EqMemTrans L Q N.isNat 
  := {eqMemTrans := K.eqNatTrans}

instance {P : Sort u} {T : Type v} 
  {L : Logic P} [N : IsNat P T] [Q : LEq P T] [A : Add T] 
  [K : EqMemTrans L Q N.isNat] : EqNatTrans L N Q
  := {eqNatTrans := K.eqMemTrans}

def eqNatTrans {P : Sort u} {T : Sort v} 
  {L : Logic P} [N : IsNat P T] [Q : LEq P T] [K : EqNatTrans L N Q]
  {x y z : T} := K.eqNatTrans x y z

def eqNatTrans' {P : Sort u} {T : Sort v} 
  {L : Logic P} [N : IsNat P T] [Q : LEq P T] [K : EqNatTrans L N Q]
  {y x z : T} (Ny : L |- nat y) (Nx : L |- nat x) (Nz : L |- nat z)  
  := K.eqNatTrans x y z Nx Ny Nz

-- w/ Implied Nats
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