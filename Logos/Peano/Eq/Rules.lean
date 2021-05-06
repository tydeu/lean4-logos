import Logos.Peano.Nat
import Logos.Logic.Rel.Rules
import Logos.Logic.Eq.Syntax

universes u v w
variable {P : Sort u} {T : Sort v}

open Logos.Notation
namespace Logos.Peano

--------------------------------------------------------------------------------
-- Closure
--------------------------------------------------------------------------------

-- Axiom N5
class NatEqNat (L : Logic P) (N : SNat P T) (Q : SEq P T) :=
  toFun : (a b : T) -> (L |- nat b) -> (L |- a = b) -> (L |- nat a)

abbrev natEqNat {L : Logic P} [N : SNat P T] [Q : SEq P T] 
  [K : NatEqNat L N Q] {a b} := K.toFun a b

abbrev natEq {L : Logic P} [N : SNat P T] [Q : SEq P T] 
  [K : NatEqNat L N Q] {a b} := K.toFun a b

--------------------------------------------------------------------------------
-- Reflexivity
-- x -> (x = x)
--------------------------------------------------------------------------------

-- Axiom N2
class EqNatRefl (L : Logic P) (N : SNat P T) (Q : SEq P T) :=
  toFun : (x : T) -> (L |- nat x) -> (L |- x = x)

abbrev eqNatRefl {L : Logic P} [N : SNat P T] [Q : SEq P T] 
  [K : EqNatRefl L N Q] {x} := K.toFun x

instance iReflTOfEqNatRefl {L : Logic P} [N : SNat P T] [Q : SEq P T]
  [K : EqNatRefl L N Q] : ReflT L Q.toFun N.mem := {toFun := K.toFun}

instance iEqNatReflOfReflT {L : Logic P} [N : SNat P T] [Q : SEq P T]
  [K : ReflT L Q.toFun N.mem] : EqNatRefl L N Q := {toFun := K.toFun}

--------------------------------------------------------------------------------
-- Symmetry
-- x = y |- y = x
--------------------------------------------------------------------------------

-- Axiom N3
class EqNatSymm (L : Logic P) (N : SNat P T) (Q : SEq P T) :=
  toFun : (x y : T) -> (L |- nat x) -> (L |- nat y) ->
    (L |- x = y) -> (L |- y = x)

abbrev eqNatSymm {L : Logic P} [N : SNat P T] [Q : SEq P T] 
  [K : EqNatSymm L N Q] {x y} := K.toFun x y

instance iSymmTOfEqNatSymm {L : Logic P} [N : SNat P T] [Q : SEq P T]
  [K : EqNatSymm L N Q] : SymmT L Q.toFun N.mem := {toFun := K.toFun}

instance iEqNatSymmOfSymmT  {L : Logic P} [N : SNat P T] [Q : SEq P T]
  [K : SymmT L Q.toFun N.mem] : EqNatSymm L N Q := {toFun := K.toFun}

--------------------------------------------------------------------------------
-- Transitivity
-- x = y, y = z |- x = z
--------------------------------------------------------------------------------

-- Axiom N4
class EqNatTrans  (L : Logic P) (N : SNat P T) (Q : SEq P T) :=
  toFun : (x y z : T) -> (L |- nat x) -> (L |- nat y) -> (L |- nat z) -> 
    (L |- x = y) -> (L |- y = z) -> (L |- x = z)

abbrev eqNatTrans {L : Logic P} [N : SNat P T] [Q : SEq P T] 
  [K : EqNatTrans L N Q] {x y z} := K.toFun x y z

abbrev eqNatTrans'  {L : Logic P} [N : SNat P T] [Q : SEq P T] 
  [K : EqNatTrans L N Q] {y x z} (Ny Nx Nz) := K.toFun x y z Nx Ny Nz

instance iTransTOfEqNatTrans  {L : Logic P} [N : SNat P T] [Q : SEq P T]
  [K : EqNatTrans L N Q] : TransT L Q.toFun N.mem := {toFun := K.toFun}

instance iEqNatTransOfEqTransT  {L : Logic P} [N : SNat P T] [Q : SEq P T]
  [K : TransT L Q.toFun N.mem] : EqNatTrans L N Q := {toFun := K.toFun}

-- w/ Implied Nats
class EqTransNat (L : Logic P) (N : SNat P T) (Q : SEq P T) :=
  toFun : (a b c : T) -> 
    (L |- nat c) -> (L |- a = b) -> (L |- b = c) -> (L |- a = c)

abbrev eqTransNat {L : Logic P} [N : SNat P T] [Q : SEq P T] 
  [K : EqTransNat L N Q] (b) {a c} := K.toFun a b c

abbrev eqTransNat'  {L : Logic P} [N : SNat P T] [Q : SEq P T] 
  [K : EqTransNat L N Q] {a b c} := K.toFun a b c

--------------------------------------------------------------------------------
-- Euclideaness
--------------------------------------------------------------------------------

-- Left Euclidean
-- b = a, c = a |- b = c

class EqNatLeftEuc (L : Logic P) (N : SNat P T) (Q : SEq P T) :=
  toFun : (a b c : T) -> 
    (L |- nat a) -> (L |- nat b) -> (L |- nat c) -> 
    (L |- b = a) -> (L |- c = a) -> (L |- b = c)

abbrev eqNatLeftEuc {L : Logic P} [N : SNat P T] [Q : SEq P T]
  [K : EqNatLeftEuc L N Q] {a b c} := K.toFun a b c 

instance iLeftEucTOfEqNatLeftEuc 
  {L : Logic P} [N : SNat P T] [Q : SEq P T] 
  [K : EqNatLeftEuc L N Q] : LeftEucT L Q.toFun N.mem := 
  {toFun := K.toFun}

instance iEqNatLeftEucOfLeftEucT 
  {L : Logic P} [N : SNat P T] [Q : SEq P T] 
  [K : LeftEucT L Q.toFun N.mem] : EqNatLeftEuc L N Q := 
  {toFun := K.toFun}

-- w/ Implied Nats
class EqLeftEucNat (L : Logic P) (N : SNat P T) (Q : SEq P T) :=
  toFun : (a b c : T) -> (L |- nat a) -> 
    (L |- b = a) -> (L |- c = a) -> (L |- b = c)

abbrev eqLeftEucNat {L : Logic P} [N : SNat P T] [Q : SEq P T]
  [K : EqLeftEucNat L N Q] {a b c} := K.toFun a b c 

-- Right Euclidean
-- a = b, a = c |- b = c

class EqNatRightEuc (L : Logic P) (N : SNat P T) (Q : SEq P T) :=
  toFun : (a b c : T) -> 
    (L |- nat a) -> (L |- nat b) -> (L |- nat c) -> 
    (L |- a = b) -> (L |- a = c) -> (L |- b = c)

abbrev eqNatRightEuc {L : Logic P} [N : SNat P T] [Q : SEq P T]
  [K : EqNatRightEuc L N Q] {a b c} := K.toFun a b c 

instance iRightEucTOfEqNatRightEuc 
  {L : Logic P} [N : SNat P T] [Q : SEq P T] 
  [K : EqNatRightEuc L N Q] : RightEucT L Q.toFun N.mem := 
  {toFun := K.toFun}

instance iEqNatRightEucOfEqRightEucT  
  {L : Logic P} [N : SNat P T] [Q : SEq P T] 
  [K : RightEucT L Q.toFun N.mem] : EqNatRightEuc L N Q := 
  {toFun := K.toFun}

--------------------------------------------------------------------------------
-- Left Transitive Join
--------------------------------------------------------------------------------

-- x = a, y = b, a = b |- x = y

class EqNatJoin (L : Logic P) (N : SNat P T) (Q : SEq P T) :=
  toFun : (x y a b : T) -> 
    (L |- nat x) -> (L |- nat y) -> (L |- nat a) -> (L |- nat b) ->
    (L |- x = a) -> (L |- y = b) -> (L |- a = b) -> (L |- x = y)

abbrev eqNatJoin {L : Logic P} [N : SNat P T] [Q : SEq P T]
  [K : EqNatJoin L N Q] {x y a b} := K.toFun x y a b 

instance iLeftTransJoinTOfEqNatJoin {L : Logic P} [N : SNat P T] [Q : SEq P T] 
  [K : EqNatJoin L N Q] : LeftTransJoinT L Q.toFun Q.toFun N.mem := {toFun := K.toFun}

instance iEqNatJoinOfLeftTransJoinT {L : Logic P} [N : SNat P T] [Q : SEq P T] 
  [K : LeftTransJoinT L Q.toFun Q.toFun N.mem] : EqNatJoin L N Q := {toFun := K.toFun}

-- a = b, x = a, y = b |- x = y

abbrev eqNatJoin' {L : Logic P} 
  [N : SNat P T] [Q : SEq P T] [K : EqNatJoin L N Q] {a b x y}
  (Na Nb Nx Ny Qab Qxa Qyb) := K.toFun x y a b Nx Ny Na Nb Qxa Qyb Qab
