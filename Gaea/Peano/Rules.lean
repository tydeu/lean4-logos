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
def NatZero {P : Sort u} (L : Logic P) (T : Type v) [Zero T] [Nat P T] :=
  L |- nat (0 : T)

-- Axiom 2
def EqNatRefl {P : Sort u} (L : Logic P) (T : Sort v) [Nat P T] [LEq P T] :=
  (x : T) -> (L |- nat x) -> (L |- x = x)

-- Axiom 3
def EqNatSymm {P : Sort u} (L : Logic P) (T : Sort v) [Nat P T] [LEq P T] :=
  (x y : T) -> (L |- nat x) -> (L |- nat y) ->
    (L |- x = y) -> (L |- y = x)

-- Axiom 4
def EqNatTrans {P : Sort u} (L : Logic P) (T : Sort v) [Nat P T] [LEq P T] :=
  (x y z : T) -> (L |- nat x) -> (L |- nat y) -> (L |- nat z) -> 
    (L |- x = y) -> (L |- y = z) -> (L |- x = z)

-- Axiom 5
def NatEq {P : Sort u} (L : Logic P) (T : Sort v) [Nat P T] [LEq P T] :=
  (a b : T) -> (L |- nat b) -> (L |- a = b) -> (L |- nat a)

-- Axiom 6
def NatSuccNat {P : Sort u} (L : Logic P) (T : Sort v) [Nat P T] [Succ T]:=
  (n : T) -> (L |- nat n) -> (L |- nat (S n))

-- Axiom 7a
def SuccNatSubst 
  {P : Sort u} (L : Logic P) (T : Sort v) [Nat P T] [LEq P T] [Succ T]  :=
  (m n : T) -> (L |- nat m) -> (L |- nat n) -> 
    (L |- m = n) -> (L |- S m = S n)

-- Axiom 7b
def SuccNatInj 
  {P : Sort u} (L : Logic P) (T : Sort v) [Nat P T] [LEq P T] [Succ T] :=
  (m n : T) -> (L |- nat m) -> (L |- nat n) -> 
    (L |- S m = S n) -> (L |- m = n)

-- Axiom 8
def SuccNatEqZeroFalse 
  {P : Sort u} (L : Logic P) (T : Type v) 
  [Nat P T] [LEq P T] [Succ T] [Zero T] [False P] :=
  (m n : T) -> (L |- nat m) -> (L |- nat n) -> 
    (L |- S n = 0) -> (L |- false)

-- Axiom 9
-- Induction over predicates
def NatInduction 
  {P : Sort u} (L : Logic P) (T : Type v) [Nat P T] [Zero T] [Succ T] := 
  (f : T -> P) -> (L |- f 0) -> 
  ((n : T) -> (L |- nat n) -> (L |- f n) -> (L |- f (S n))) ->
  ((n : T) -> (L |- nat n) -> (L |- f n))

-- Axiom 9 (Alt)
-- Induction over schemas
def NatInduction'
  {P : Sort u} (L : Logic P) (T : Type v) [Nat P T] [Zero T] [Succ T] := 
  (f : T -> Sort w) -> f 0 ->
  ((n : T) -> (L |- nat n) -> (f n -> f (S n))) ->
  ((n : T) -> (L |- nat n) -> f n)

--------------------------------------------------------------------------------
-- Addition Axioms
--------------------------------------------------------------------------------

-- Axiom 1
def AddNatZeroEqNat 
  {P : Sort u} (L : Logic P) (T : Type v) [LEq P T] [Nat P T] [Zero T] [Add T] :=
  (a : T) -> (L |- nat a) -> (L |- a + 0 = a)

-- Axiom 2
def AddNatSuccEqSucc 
  {P : Sort u} (L : Logic P) (T : Type v) [LEq P T] [Nat P T] [Succ T] [Add T] := 
  (a b : T) -> (L |- nat a) -> (L |- nat b) -> (L |- a + S b = S (a + b))

--------------------------------------------------------------------------------
-- Multiplication Axioms
--------------------------------------------------------------------------------

-- Axiom 1
def MulNatZeroEqZero 
  {P : Sort u} (L : Logic P) (T : Type v) [LEq P T] [Nat P T] [Zero T] [Mul T] :=
  (a b : T) -> (L |- nat a) -> (L |- nat b) -> (L |- a * 0 = 0)

-- Axiom 2
def MulNatSuccEqAddMul 
  {P : Sort u} (L : Logic P) (T : Type v) 
  [LEq P T] [Nat P T] [Succ T] [Add T] [Mul T] := 
  (a b : T) -> (L |- nat a) -> (L |- nat b) -> (L |- a + S b = a + S (a * b))

end Gaea.Peano.Rules
