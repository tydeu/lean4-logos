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
-- x -> (x = x)
--------------------------------------------------------------------------------

-- Axiom N2
class EqNatRefl {P : Sort u} {T : Sort v} 
  (L : Logic P) (N : IsNat P T) (Q : LEq P T) :=
  (eqNatRefl : (x : T) -> (L |- nat x) -> (L |- x = x))

instance iEqReflTOfEqNatRefl {P : Sort u} {T : Sort v} 
  {L : Logic P} [N : IsNat P T] [Q : LEq P T]
  [K : EqNatRefl L N Q] : EqReflT L Q N.isNat 
  := {eqReflT := K.eqNatRefl}

instance iEqNatReflTOfEqRefl {P : Sort u} {T : Sort v} 
  {L : Logic P} [N : IsNat P T] [Q : LEq P T]
  [K : EqReflT L Q N.isNat] : EqNatRefl L N Q
  := {eqNatRefl := K.eqReflT}

def eqNatRefl {P : Sort u} {T : Sort v} 
  {L : Logic P} [N : IsNat P T] [Q : LEq P T] [K : EqNatRefl L N Q]
  {x : T} := K.eqNatRefl x

--------------------------------------------------------------------------------
-- Symmetry
-- (x = y) -> (y = x)
--------------------------------------------------------------------------------

-- Axiom N3
class EqNatSymm {P : Sort u} {T : Sort v} 
  (L : Logic P) (N : IsNat P T) (Q : LEq P T) :=
  (eqNatSymm : (x y : T) -> (L |- nat x) -> (L |- nat y) ->
    (L |- x = y) -> (L |- y = x))

instance iEqSymmTOfEqNatSymm {P : Sort u} {T : Sort v} 
  {L : Logic P} [N : IsNat P T] [Q : LEq P T]
  [K : EqNatSymm L N Q] : EqSymmT L Q N.isNat 
  := {eqSymmT := K.eqNatSymm}

instance iEqNatSymmTOfEqSymm {P : Sort u} {T : Sort v} 
  {L : Logic P} [N : IsNat P T] [Q : LEq P T]
  [K : EqSymmT L Q N.isNat] : EqNatSymm L N Q
  := {eqNatSymm := K.eqSymmT}

def eqNatSymm {P : Sort u} {T : Sort v} 
  {L : Logic P} [N : IsNat P T] [Q : LEq P T] [K : EqNatSymm L N Q]
  {x y : T} := K.eqNatSymm x y

--------------------------------------------------------------------------------
-- Transitivity
-- (x = y) /\ (y = z) -> (x = z)
--------------------------------------------------------------------------------

-- Axiom N4
class EqNatTrans {P : Sort u} {T : Sort v} 
  (L : Logic P) (N : IsNat P T) (Q : LEq P T) :=
  (eqNatTrans : (x y z : T) -> (L |- nat x) -> (L |- nat y) -> (L |- nat z) -> 
    (L |- x = y) -> (L |- y = z) -> (L |- x = z))

instance iEqTransTOfEqNatTrans {P : Sort u} {T : Sort v} 
  {L : Logic P} [N : IsNat P T] [Q : LEq P T]
  [K : EqNatTrans L N Q] : EqTransT L Q N.isNat 
  := {eqTransT := K.eqNatTrans}

instance iEqNatTransTOfEqTrans {P : Sort u} {T : Sort v} 
  {L : Logic P} [N : IsNat P T] [Q : LEq P T]
  [K : EqTransT L Q N.isNat] : EqNatTrans L N Q
  := {eqNatTrans := K.eqTransT}

def eqNatTrans {P : Sort u} {T : Sort v} 
  {L : Logic P} [N : IsNat P T] [Q : LEq P T] [K : EqNatTrans L N Q]
  {x y z : T} := K.eqNatTrans x y z

def eqNatTrans' {P : Sort u} {T : Sort v} 
  {L : Logic P} [N : IsNat P T] [Q : LEq P T] [K : EqNatTrans L N Q]
  {y x z : T} (Ny : L |- nat y) (Nx : L |- nat x) (Nz : L |- nat z)  
  := K.eqNatTrans x y z Nx Ny Nz

-- w/ Implied Nats
class EqTransNat {P : Sort u} {T : Sort v} 
  (L : Logic P) (N : IsNat P T) (Q : LEq P T) :=
  (eqTransNat : (a b c : T) -> 
    (L |- nat c) -> (L |- a = b) -> (L |- b = c) -> (L |- a = c))

def eqTransNat {P : Sort u} {T : Sort v} 
{L : Logic P} [N : IsNat P T] [Q : LEq P T] [K : EqTransNat L N Q]
{a : T} (b : T) {c : T} := K.eqTransNat a b c

def eqTransNat' {P : Sort u} {T : Sort v} 
{L : Logic P} [N : IsNat P T] [Q : LEq P T] [K : EqTransNat L N Q]
{a b c : T} := K.eqTransNat a b c

--------------------------------------------------------------------------------
-- Join
--------------------------------------------------------------------------------

-- (x = a) /\ (y = b) /\ (a = b) -> (x = y)

class EqNatJoin {P : Sort u} {T : Sort v} 
  (L : Logic P) (N : IsNat P T) (Q : LEq P T) :=
  (eqNatJoin : (x y a b : T) -> 
    (L |- nat x) -> (L |- nat y) -> (L |- nat a) -> (L |- nat b) ->
    (L |- x = a) -> (L |- y = b) -> (L |- a = b) -> (L |- x = y))

instance iEqJoinTOfEqNatJoin {P : Sort u} {T : Sort v} 
  {L : Logic P} [N : IsNat P T] [Q : LEq P T] 
  [K : EqNatJoin L N Q] : EqJoinT L Q N.isNat 
  := {eqJoinT := K.eqNatJoin}

instance iEqNatJoinTOfEqJoin {P : Sort u} {T : Sort v} 
  {L : Logic P} [N : IsNat P T] [Q : LEq P T] 
  [K : EqJoinT L Q N.isNat] : EqNatJoin L N Q 
  := {eqNatJoin := K.eqJoinT}

def eqNatJoin {P : Sort u} {T : Sort v} 
  {L : Logic P} [N : IsNat P T] [Q : LEq P T]
  [K : EqNatJoin L N Q] {x y a b : T} := K.eqNatJoin x y a b 

-- (a = b) /\ (x = a) /\ (y = b) -> (x = y)

def eqNatJoin' {P : Sort u} {T : Sort v} 
  {L : Logic P} [N : IsNat P T] [Q : LEq P T]
  [K : EqNatJoin L N Q] {a b x y : T} 
  : (L |- nat a) -> (L |- nat b) -> (L |- nat x) -> (L |- nat y) ->
    (L |- a = b) -> (L |- x = a) -> (L |- y = b) ->  (L |- x = y)
  := fun Na Nb Nx Ny Qab Qxa Qyb => K.eqNatJoin x y a b Nx Ny Na Nb Qxa Qyb Qab

--------------------------------------------------------------------------------
-- Euclideaness
--------------------------------------------------------------------------------

-- Left Euclidean
-- (b = a) /\ (c = a) -> (b = c)

class EqNatLeftEuc {P : Sort u} {T : Sort v} 
  (L : Logic P) (N : IsNat P T) (Q : LEq P T) :=
  (eqNatLeftEuc : (a b c : T) -> 
    (L |- nat a) -> (L |- nat b) -> (L |- nat c) -> 
    (L |- b = a) -> (L |- c = a) -> (L |- b = c))

instance iEqLeftEucTOfEqNatLeftEuc {P : Sort u} {T : Sort v} 
  {L : Logic P} [N : IsNat P T] [Q : LEq P T] [K : EqNatLeftEuc L N Q] 
  : EqLeftEucT L Q N.isNat := {eqLeftEucT := K.eqNatLeftEuc}

instance iEqNatLeftEucTOfEqLeftEuc {P : Sort u} {T : Sort v} 
  {L : Logic P} [N : IsNat P T] [Q : LEq P T] [K : EqLeftEucT L Q N.isNat] 
  : EqNatLeftEuc L N Q := {eqNatLeftEuc := K.eqLeftEucT}

def eqNatLeftEuc {P : Sort u} {T : Sort v} 
  {L : Logic P} [N : IsNat P T] [Q : LEq P T]
  [K : EqNatLeftEuc L N Q] {a b c : T} := K.eqNatLeftEuc a b c 

-- w/ Implied Nats
class EqLeftEucNat {P : Sort u} {T : Sort v} 
  (L : Logic P) (N : IsNat P T) (Q : LEq P T) :=
  (eqLeftEucNat : (a b c : T) -> (L |- nat a) -> 
    (L |- b = a) -> (L |- c = a) -> (L |- b = c))

def eqLeftEucNat {P : Sort u} {T : Sort v} 
  {L : Logic P} [N : IsNat P T] [Q : LEq P T]
  [K : EqLeftEucNat L N Q] {a b c : T} := K.eqLeftEucNat a b c 

-- Right Euclidean
-- (a = b) /\ (a = c) -> (b = c)

class EqNatRightEuc {P : Sort u} {T : Sort v} 
  (L : Logic P) (N : IsNat P T) (Q : LEq P T) :=
  (eqNatRightEuc : (a b c : T) -> 
    (L |- nat a) -> (L |- nat b) -> (L |- nat c) -> 
    (L |- a = b) -> (L |- a = c) -> (L |- b = c))

instance iEqRightEucTOfEqNatRightEuc {P : Sort u} {T : Sort v} 
  {L : Logic P} [N : IsNat P T] [Q : LEq P T] [K : EqNatRightEuc L N Q] 
  : EqRightEucT L Q N.isNat := {eqRightEucT := K.eqNatRightEuc}

instance iEqNatRightEucTOfEqRightEuc {P : Sort u} {T : Sort v} 
  {L : Logic P} [N : IsNat P T] [Q : LEq P T] [K : EqRightEucT L Q N.isNat] 
  : EqNatRightEuc L N Q := {eqNatRightEuc := K.eqRightEucT}

def eqNatRightEuc {P : Sort u} {T : Sort v} 
  {L : Logic P} [N : IsNat P T] [Q : LEq P T]
  [K : EqNatLeftEuc L N Q] {a b c : T} := K.eqNatLeftEuc a b c 

end Gaea.Peano