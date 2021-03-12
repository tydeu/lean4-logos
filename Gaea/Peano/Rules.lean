import Gaea.Logic
import Gaea.Peano.Nat

import Gaea.Syntax.Math
import Gaea.Syntax.Logic
import Gaea.Syntax.Notation
import Gaea.Logic.Notation

open Gaea.Logic
open Gaea.Syntax

namespace Gaea.Peano.Rules

universes u v w

-- Natural Axioms

-- Axiom 1
def NatZero {P : Sort u} (L : Logic P) (N : Type v) [Zero N] [Nat P N] :=
  L |- nat (0 : N)

-- Axiom 2
def EqNatRefl {P : Sort u} (L : Logic P) (N : Sort v) [Nat P N] [LEq P N] :=
  (x : N) -> (L |- nat x) -> (L |- x = x)

-- Axiom 3
def EqNatSymm {P : Sort u} (L : Logic P) (N : Sort v) [Nat P N] [LEq P N] :=
  (x y : N) -> (L |- nat x) -> (L |- nat y) ->
    (L |- x = y) -> (L |- y = x)

-- Axiom 4
def EqNatTrans {P : Sort u} (L : Logic P) (N : Sort v) [Nat P N] [LEq P N] :=
  (x y z : N) -> (L |- nat x) -> (L |- nat y) -> (L |- nat z) -> 
    (L |- x = y) -> (L |- y = z) -> (L |- x = z)

-- Axiom 5
def NatEq {P : Sort u} (L : Logic P) (N : Sort v) [Nat P N] [LEq P N] :=
  (a b : N) -> (L |- nat b) -> (L |- a = b) -> (L |- nat a)

-- Axiom 6
def NatSuccNat {P : Sort u} (L : Logic P) (N : Sort v) [Nat P N] [Succ N]:=
  (n : N) -> (L |- nat n) -> (L |- nat (S n))

-- Axiom 7a
def SuccNatSubst 
  {P : Sort u} (L : Logic P) (N : Sort v) [Nat P N] [LEq P N] [Succ N]  :=
  (m n : N) -> (L |- nat m) -> (L |- nat n)-> 
    (L |- m = n) -> (L |- S m = S n)

-- Axiom 7b
def SuccNatInj 
  {P : Sort u} (L : Logic P) (N : Sort v) [Nat P N] [LEq P N] [Succ N] :=
  (m n : N) -> (L |- nat m) -> (L |- nat n) -> 
    (L |- S m = S n) -> (L |- m = n)

-- Axiom 8
def SuccNatEqZeroFalse 
  {P : Sort u} (L : Logic P) (N : Type v) 
  [Nat P N] [LEq P N] [Succ N] [Zero N] [False P] :=
  (m n : N) -> (L |- nat m) -> (L |- nat n) -> 
    (L |- S n = 0) -> (L |- false)

-- Axiom 9
def NatInduction 
  {P : Sort u} (L : Logic P) (N : Type v) [Nat P N] [Zero N] [Succ N] := 
  (f : N -> P) -> (L |- f 0) -> 
  ((n : N) -> (L |- nat n) -> (L |- f n) -> (L |- f (S n))) ->
  ((n : N) -> (L |- nat n) -> (L |- f n))

def NatInduction'
  {P : Sort u} (L : Logic P) (N : Type v) [Nat P N] [Zero N] [Succ N] := 
  (f : N -> Sort w) -> f 0 ->
  ((n : N) -> (L |- nat n) -> (f n -> f (S n))) ->
  ((n : N) -> (L |- nat n) -> f n)

-- Addition Axioms

def AddNatZeroEqNat 
  {P : Sort u} (L : Logic P) (N : Type v) [LEq P N] [Nat P N] [Zero N] [Add N] :=
  (a : N) -> (L |- nat a) -> (L |- a + 0 = a)

def AddNatSuccEqSucc 
  {P : Sort u} (L : Logic P) (N : Type v) [LEq P N] [Nat P N] [Succ N] [Add N] := 
  (a b : N) -> (L |- nat a) -> (L |- nat b) -> (L |- a + S b = S (a + b))

-- Multiplication Axioms

def MulNatZeroEqZero 
  {P : Sort u} (L : Logic P) (N : Type v) [LEq P N] [Nat P N] [Zero N] [Mul N] :=
  (a b : N) -> (L |- nat a) -> (L |- nat b) -> (L |- a * 0 = 0)

def MulNatSuccEqAddMul 
  {P : Sort u} (L : Logic P) (N : Type v) 
  [LEq P N] [Nat P N] [Succ N] [Add N] [Mul N] := 
  (a b : N) -> (L |- nat a) -> (L |- nat b) -> (L |- a + S b = a + S (a * b))

end Gaea.Peano.Rules
