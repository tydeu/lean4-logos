import Gaea.Logic
import Gaea.Logic.Notation
import Gaea.Math.Notation
import Gaea.Peano.Nat

universes u v w

open Gaea.Math
open Gaea.Logic

namespace Gaea.Peano

--------------------------------------------------------------------------------
-- Logic Rules
--------------------------------------------------------------------------------

def forallNatIntro {P : Sort u} {T : Type v} {L : Logic P} 
  [N : IsNat P T] [Fa : LForall P T] [If : LIf P] [ForallIntro L Fa] [IfIntro L If]
  {f : T -> P} (F : (a : T) -> (L |- nat a) -> (L |- f a))
  : L |- forall a => nat a -> f a
  := forallIntro fun a => ifIntro fun Na => F a Na

def forallNatElim {P : Sort u} {T : Type v} {L : Logic P} 
  [N : IsNat P T] [Fa : LForall P T] [If : LIf P] [ForallElim L Fa] [IfElim L If]
  {f : T -> P} (p : L |- forall (a : T) => nat a -> f a) 
  {a : T} (Na : L |- nat a) : L |- f a
  := ifElim (forallElim p a) Na

--------------------------------------------------------------------------------
-- Natural Axioms
--------------------------------------------------------------------------------

-- Axiom 1
class NatZero {P : Sort u} {T : Type v} 
  (L : Logic P) (N : IsNat P T) (Z : Zero T) :=
  (natZero : L |- nat (0 : T))

def natZero {P : Sort u} (L : Logic P) (T : Type v) 
  [N : IsNat P T] [Z : Zero T] [K : NatZero L N Z] := K.natZero

def nat0 {P : Sort u} {T : Type v} 
  {L : Logic P} [N : IsNat P T] [Z : Zero T] [K : NatZero L N Z] := K.natZero

-- Axiom 2
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

-- Axiom 3
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

-- Axiom 4
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

-- Axiom 5
class NatEqNat {P : Sort u} {T : Sort v} 
  (L : Logic P) (N : IsNat P T) (Q : LEq P T) :=
  (natEqNat : (a b : T) -> (L |- nat b) -> (L |- a = b) -> (L |- nat a))

def natEqNat {P : Sort u} {T : Sort v} 
  {L : Logic P} [N : IsNat P T] [Q : LEq P T] [K : NatEqNat L N Q] 
  {a b : T} := K.natEqNat a b

def natEq {P : Sort u} {T : Sort v} 
  {L : Logic P} [N : IsNat P T] [Q : LEq P T] [K : NatEqNat L N Q] 
  {a b : T} := K.natEqNat a b

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

-- Axiom 9
-- Induction over predicates
class NatInduction {P : Sort u} {T : Type v} 
  (L : Logic P) (N : PNat P T) := 
  (natInduction : 
    (f : T -> P) -> (L |- f 0) -> 
    ((n : T) -> (L |- nat n) -> (L |- f n) -> (L |- f (S n))) ->
    ((n : T) -> (L |- nat n) -> (L |- f n)))

def natInduction {P : Sort u} {T : Type v} {L : Logic P} 
  [N : PNat P T] [I : NatInduction L N] {f : T -> P} := I.natInduction f

-- Axiom 9 (Alt)
-- Induction over schemas
class NatInduction' {P : Sort u} {T : Type v} 
  (L : Logic P) (N : PNat P T) := 
  (natInduction' : (f : T -> Sort w) -> f 0 ->
    ((n : T) -> (L |- nat n) -> (f n -> f (S n))) ->
    ((n : T) -> (L |- nat n) -> f n))

def natInduction' {P : Sort u} {T : Type v} 
  (L : Logic P) [N : PNat P T] [I : NatInduction' L N] := I.natInduction'

end Gaea.Peano
