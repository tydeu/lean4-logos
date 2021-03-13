import Gaea.Logic
import Gaea.Peano.Nat

import Gaea.Syntax.Math
import Gaea.Syntax.Logic
import Gaea.Syntax.Notation
import Gaea.Logic.Notation

universes u v w

open Gaea.Logic
open Gaea.Syntax

namespace Gaea.Peano.Rules

--------------------------------------------------------------------------------
-- Natural Axioms
--------------------------------------------------------------------------------

-- Axiom 1
def NatZero  {P : Sort u} {T : Type v} 
  (L : Logic P) (N : Nat P T) (Z : Zero T) :=
  L |- nat (0 : T)

-- Axiom 2
def EqNatRefl {P : Sort u} {T : Sort v} 
  (L : Logic P) (N : Nat P T) (Eq : LEq P T) :=
  (x : T) -> (L |- nat x) -> (L |- x = x)

-- Axiom 3
def EqNatSymm {P : Sort u} {T : Sort v} 
  (L : Logic P) (N : Nat P T) (Eq : LEq P T) :=
  (x y : T) -> (L |- nat x) -> (L |- nat y) ->
    (L |- x = y) -> (L |- y = x)

-- Axiom 4
def EqNatTrans {P : Sort u} {T : Sort v} 
  (L : Logic P) (N : Nat P T) (Eq : LEq P T) :=
  (x y z : T) -> (L |- nat x) -> (L |- nat y) -> (L |- nat z) -> 
    (L |- x = y) -> (L |- y = z) -> (L |- x = z)

-- Axiom 5
def NatEqNat {P : Sort u} {T : Sort v} 
  (L : Logic P) (N : Nat P T) (Eq : LEq P T) :=
  (a b : T) -> (L |- nat b) -> (L |- a = b) -> (L |- nat a)

-- Axiom 6
def NatSuccNat {P : Sort u} {T : Sort v} 
  (L : Logic P) (N : Nat P T) (Su : Succ T) :=
  (n : T) -> (L |- nat n) -> (L |- nat (S n))

-- Axiom 7a
def EqNatToEqSucc {P : Sort u} {T : Sort v} 
  (L : Logic P) (N : Nat P T) (Eq : LEq P T) (Su : Succ T) :=
  (m n : T) -> (L |- nat m) -> (L |- nat n) -> 
    (L |- m = n) -> (L |- S m = S n)

-- Axiom 7b
def EqSuccToEqNat {P : Sort u} {T : Sort v} 
  (L : Logic P) (N : Nat P T) (Eq : LEq P T) (Su : Succ T) :=
  (m n : T) -> (L |- nat m) -> (L |- nat n) -> 
    (L |- S m = S n) -> (L |- m = n)

-- Axiom 8
def SuccNatEqZeroFalse {P : Sort u} {T : Type v} 
  (L : Logic P) (N : Nat P T) (Eq : LEq P T) (Z : Zero T) (Su : Succ T) [False P] :=
  (m n : T) -> (L |- nat m) -> (L |- nat n) -> 
    (L |- S n = 0) -> (L |- false)

-- Axiom 9
-- Induction over predicates
def NatInduction {P : Sort u} {T : Type v} 
  (L : Logic P) (N : Nat P T) (Z : Zero T) (Su : Succ T) := 
  (f : T -> P) -> (L |- f 0) -> 
  ((n : T) -> (L |- nat n) -> (L |- f n) -> (L |- f (S n))) ->
  ((n : T) -> (L |- nat n) -> (L |- f n))

-- Axiom 9 (Alt)
-- Induction over schemas
def NatInduction' {P : Sort u} {T : Type v} 
  (L : Logic P) (N : Nat P T) (Z : Zero T) (Su : Succ T) := 
  (f : T -> Sort w) -> f 0 ->
  ((n : T) -> (L |- nat n) -> (f n -> f (S n))) ->
  ((n : T) -> (L |- nat n) -> f n)

--------------------------------------------------------------------------------
-- Addition Axioms
--------------------------------------------------------------------------------

-- Axiom 1
def AddNatZeroEqNat {P : Sort u} {T : Type v} 
  (L : Logic P) (N : Nat P T) (Eq : LEq P T) (A : Add T) (Z : Zero T) :=
  (a : T) -> (L |- nat a) -> (L |- a + 0 = a)

-- Axiom 2
def AddNatSuccEqSucc {P : Sort u} {T : Type v} 
  (L : Logic P) (N : Nat P T)  (Eq : LEq P T) (A : Add T) (Su : Succ T) := 
  (a b : T) -> (L |- nat a) -> (L |- nat b) -> (L |- a + S b = S (a + b))

--------------------------------------------------------------------------------
-- Multiplication Axioms
--------------------------------------------------------------------------------

-- Axiom 1
def MulNatZeroEqZero {P : Sort u} {T : Type v} 
  (L : Logic P) (N : Nat P T) (Eq : LEq P T) (M : Mul T) (Z : Zero T)  :=
  (a : T) -> (L |- nat a) -> (L |- a * 0 = 0)

-- Axiom 2
def MulNatSuccEqAddMul {P : Sort u} {T : Type v} 
  (L : Logic P) (N : Nat P T) (Eq : LEq P T) (M : Mul T) (A : Add T) (Su : Succ T) := 
  (a b : T) -> (L |- nat a) -> (L |- nat b) -> (L |- a + S b = a + S (a * b))

end Gaea.Peano.Rules
