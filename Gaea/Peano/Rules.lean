import Gaea.Logic
import Gaea.Peano.Nat

import Gaea.Syntax.Math
import Gaea.Syntax.Logic
import Gaea.Syntax.Notation
import Gaea.Logic.Notation

universes u v w

open Gaea.Logic
open Gaea.Syntax

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
-- Natural Rules
--------------------------------------------------------------------------------

-- Axiom 1
class NatZero {P : Sort u} {T : Type v} 
  (L : Logic P) (N : IsNat P T) (Z : Zero T) :=
  (natZero : L |- nat (0 : T))

def natZero {P : Sort u} {T : Type v} 
  {L : Logic P} [N : IsNat P T] [Z : Zero T] [K : NatZero L N Z] := K.natZero

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
  (L : Logic P) (N : IsNat P T) (Su : Succ T) :=
  (natSuccNat : (n : T) -> (L |- nat n) -> (L |- nat (S n)))

def natSuccNat {P : Sort u} {T : Sort v} 
{L : Logic P} [N : IsNat P T] [Su : Succ T] [K : NatSuccNat L N Su] 
{n : T} := K.natSuccNat n

def natS {P : Sort u} {T : Sort v} 
{L : Logic P} [N : IsNat P T] [Su : Succ T] [K : NatSuccNat L N Su] 
{n : T} := K.natSuccNat n

-- Axiom 7a
class EqNatToEqSucc {P : Sort u} {T : Sort v} 
  (L : Logic P) (N : IsNat P T) (Q : LEq P T) (Su : Succ T) :=
  (eqNatToEqSucc : (m n : T) -> (L |- nat m) -> (L |- nat n) -> 
    (L |- m = n) -> (L |- S m = S n))

instance {P : Sort u} {T : Type v} 
  {L : Logic P} [N : IsNat P T] [Q : LEq P T] [Su : Succ T]
  [K : EqNatToEqSucc L N Q Su] : EqMemToEqFun L Q N.isNat Su.succ 
  := {eqMemToEqFun := K.eqNatToEqSucc}

instance {P : Sort u} {T : Type v} 
  {L : Logic P} [N : IsNat P T] [Q : LEq P T] [Su : Succ T]
  [K : EqMemToEqFun L Q N.isNat Su.succ] : EqNatToEqSucc L N Q Su
  := {eqNatToEqSucc := K.eqMemToEqFun}

def eqNatToEqSucc {P : Sort u} {T : Sort v} 
  {L : Logic P} [N : IsNat P T] [Q : LEq P T] [Su : Succ T]
  [K : EqNatToEqSucc L N Q Su] {m n : T} := K.eqNatToEqSucc m n

-- Axiom 7b
class EqSuccToEqNat {P : Sort u} {T : Sort v} 
  (L : Logic P) (N : IsNat P T) (Q : LEq P T) (Su : Succ T) :=
  (eqSuccToEqNat : (m n : T) -> (L |- nat m) -> (L |- nat n) -> 
    (L |- S m = S n) -> (L |- m = n))

def eqSuccToEqNat {P : Sort u} {T : Sort v} 
  {L : Logic P} [N : IsNat P T] [Q : LEq P T] [Su : Succ T]
  [K : EqSuccToEqNat L N Q Su] {m n : T} := K.eqSuccToEqNat

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

--------------------------------------------------------------------------------
-- Addition Rules
--------------------------------------------------------------------------------

-- Axiom 1
class AddNatZeroEqNat {P : Sort u} {T : Type v} 
  (L : Logic P) (N : IsNat P T) (Q : LEq P T) (A : Add T) (Z : Zero T) :=
  (addNatZeroEqNat : (a : T) -> (L |- nat a) -> (L |- a + 0 = a))

def addNatZeroEqNat {P : Sort u} {T : Type v} 
  {L : Logic P} [N : IsNat P T] [Q : LEq P T] [A : Add T] [Z : Zero T] 
  [K : AddNatZeroEqNat L N Q A Z] {a : T} := K.addNatZeroEqNat a

-- Axiom 2
class AddNatSuccEqSucc {P : Sort u} {T : Type v} 
  (L : Logic P) (N : IsNat P T) (Q : LEq P T) (A : Add T) (Su : Succ T) := 
  (addNatSuccEqSucc : (a b : T) -> (L |- nat a) -> (L |- nat b) -> 
    (L |- a + S b = S (a + b)))

def addNatSuccEqSucc {P : Sort u} {T : Type v} 
  {L : Logic P} [N : IsNat P T] [Q : LEq P T] [A : Add T] [Su : Succ T]
  [K : AddNatSuccEqSucc L N Q A Su] {a b : T} := K.addNatSuccEqSucc a b

-- Axiom 1 Commuted
class AddZeroNatEqNat {P : Sort u} {T : Type v} 
  (L : Logic P) (N : IsNat P T) (Q : LEq P T) (A : Add T) (Z : Zero T) :=
  (addZeroNatEqNat : (a : T) -> (L |- nat a) -> (L |- 0 + a = a))

def addZeroNatEqNat {P : Sort u} {T : Type v} 
  {L : Logic P} [N : IsNat P T] [Q : LEq P T] [A : Add T] [Z : Zero T] 
  [K : AddZeroNatEqNat L N Q A Z] {a : T} := K.addZeroNatEqNat a

-- Axiom 2 Commuted
class AddSuccNatEqSucc {P : Sort u} {T : Type v} 
  (L : Logic P) (N : IsNat P T) (Q : LEq P T) (A : Add T) (Su : Succ T) := 
  (addSuccNatEqSucc : (a b : T) -> (L |- nat a) -> (L |- nat b) -> 
    (L |- S a + b = S (a + b)))

def addSuccNatEqSucc {P : Sort u} {T : Type v} 
  {L : Logic P} [N : IsNat P T] [Q : LEq P T] [A : Add T] [Su : Succ T]
  [K : AddSuccNatEqSucc L N Q A Su] {a b : T} := K.addSuccNatEqSucc a b

--------------------------------------------------------------------------------
-- Multiplication Rules
--------------------------------------------------------------------------------

-- Axiom 1
class MulNatZeroEqZero {P : Sort u} {T : Type v} 
  (L : Logic P) (N : IsNat P T) (Q : LEq P T) (M : Mul T) (Z : Zero T)  :=
  (mulNatZeroEqZero : (a : T) -> (L |- nat a) -> (L |- a * 0 = 0))

def mulNatZeroEqZero {P : Sort u} {T : Type v} 
  {L : Logic P} [N : IsNat P T] [Q : LEq P T] [M : Mul T] [Z : Zero T] 
  [K : MulNatZeroEqZero L N Q M Z] {a : T} := K.mulNatZeroEqZero a

-- Axiom 2
class MulNatSuccEqAddMul {P : Sort u} {T : Type v} 
  (L : Logic P) (N : IsNat P T) (Q : LEq P T) (M : Mul T) (A : Add T) (Su : Succ T) := 
  (mulNatSuccEqAddMul : (a b : T) -> (L |- nat a) -> (L |- nat b) -> 
    (L |- a + S b = a + S (a * b)))

def mulNatSuccEqAddMul {P : Sort u} {T : Type v} 
  {L : Logic P} [N : IsNat P T] [Q : LEq P T] [M : Mul T] [A : Add T] [Su : Succ T]
  [K : MulNatSuccEqAddMul L N Q M A Su] {a b : T} := K.mulNatSuccEqAddMul a b

-- Axiom 1 Commuted
class MulZeroNatEqZero {P : Sort u} {T : Type v} 
  (L : Logic P) (N : IsNat P T) (Q : LEq P T) (M : Mul T) (Z : Zero T)  :=
  (mulZeroNatEqZero : (a : T) -> (L |- nat a) -> (L |- 0 * a = 0))

def mulZeroNatEqZero {P : Sort u} {T : Type v} 
  {L : Logic P} [N : IsNat P T] [Q : LEq P T] [M : Mul T] [Z : Zero T] 
  [K : MulZeroNatEqZero L N Q M Z] {a : T} := K.mulZeroNatEqZero a

-- Axiom 2 Commuted
class MulSuccNatEqAddMul {P : Sort u} {T : Type v} 
  (L : Logic P) (N : IsNat P T) (Q : LEq P T) (M : Mul T) (A : Add T) (Su : Succ T) := 
  (mulSuccNatEqAddMul : (a b : T) -> (L |- nat a) -> (L |- nat b) -> 
    (L |- S a + b = a + S (a * b)))

def mulSuccNatEqAddMul {P : Sort u} {T : Type v} 
  {L : Logic P} [N : IsNat P T] [Q : LEq P T] [M : Mul T] [A : Add T] [Su : Succ T]
  [K : MulSuccNatEqAddMul L N Q M A Su] {a b : T} := K.mulSuccNatEqAddMul a b

end Gaea.Peano
