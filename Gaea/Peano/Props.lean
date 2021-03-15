import Gaea.Logic
import Gaea.Peano.Nat

import Gaea.Syntax.Math
import Gaea.Syntax.Logic
import Gaea.Syntax.Notation
import Gaea.Logic.Notation

universes u v

open Gaea.Logic
open Gaea.Syntax

namespace Gaea.Peano.Props

--------------------------------------------------------------------------------
-- Natural Axioms
--------------------------------------------------------------------------------

-- Axiom 1
def natZero {P : Sort u} (T : Type v) [IsNat P T] [Zero T] : P :=
  nat (0 : T)

-- Axiom 2
def eqNatRefl {P : Sort u} (T : Sort v) 
  [IsNat P T] [LEq P T] [LIf P] [LForall P T] : P :=
  forall (x : T) => nat x -> x = x

-- Axiom 3
def eqNatSymm {P : Sort u} (T : Sort v) 
  [IsNat P T] [LEq P T] [LIf P] [LAnd P] [LForall P T] : P :=
  forall (x y : T) => nat x /\ nat y -> (x = y -> y = x)

-- Axiom 4
def eqNatTrans {P : Sort u} (T : Sort v) 
  [IsNat P T] [LEq P T] [LIf P] [LAnd P] [LForall P T] : P :=
  forall (x y z : T) => nat x /\ nat y /\ nat z -> (x = y /\ y = z -> x = z)

-- Axiom 5
def natEqNat {P : Sort u} (L : Logic P) (T : Sort v) 
  [IsNat P T] [LEq P T] [LIf P] [LAnd P] [LForall P T] : P :=
  forall (a b : T) => nat b /\ a = b -> nat a

-- Axiom 6
def natSuccNat {P : Sort u} (T : Sort v) 
  [IsNat P T] [Succ T] [LIf P] [LForall P T] : P :=
  forall (n : T) => nat n -> nat (S n)

-- Axiom 7
def eqNatIffEqSucc {P : Sort u} (T : Sort v) 
  [LEq P T] [Succ T] [IsNat P T] [LIf P] [LIff P] [LAnd P] [LForall P T] : P :=
  forall (m n : T) => nat m /\ nat n -> (m = n <-> S m = S n)

-- Axiom 7a
def eqNatToEqSucc {P : Sort u} (T : Sort v) 
  [LEq P T] [Succ T] [IsNat P T] [LIf P] [LAnd P] [LForall P T] : P :=
  forall (m n : T) => nat m /\ nat n -> (m = n -> S m = S n)

-- Axiom 7b
def eqSuccToEqNat {P : Sort u} (T : Sort v) 
  [IsNat P T] [LEq P T] [Succ T] [LIf P] [LAnd P] [LForall P T] : P :=
  forall (m n : T) => nat m /\ nat n -> (S m = S n -> m = n)

-- Axiom 8
def succNatEqZeroFalse {P : Sort u} (T : Type v) 
  [IsNat P T] [LEq P T] [LFalse P] [Zero T] [Succ T] [LIf P] [LAnd P] [LForall P T] : P :=
  forall (m n : T) => nat m /\ nat n -> (S n = 0 -> false)

-- Axiom 9
def natInduction 
  {P : Sort u} (T : Type v) 
  [IsNat P T] [Zero T] [Succ T]
  [LIf P] [LAnd P] [LForall P T] [LForall P (T -> P)]  : P := 
  forall (f : T -> P) => 
    f 0 -> 
    (forall (n : T) => nat n -> (f n -> f (S n))) ->
    (forall (n : T) => nat n -> f n)

--------------------------------------------------------------------------------
-- Addition Axioms
--------------------------------------------------------------------------------

-- Axiom 1
def addNatZeroEqNat {P : Sort u} (T : Type v) 
  [IsNat P T] [LEq P T] [Add T] [Zero T] [LIf P] [LForall P T] : P :=
  forall (a : T) => nat a -> a + 0 = a

-- Axiom 2
def addNatSuccEqSucc {P : Sort u} (T : Type v) 
  [IsNat P T] [LEq P T] [Add T] [Succ T] [LIf P] [LAnd P] [LForall P T] : P := 
  forall (a b : T) => nat a /\ nat b -> a + S b = S (a + b)

--------------------------------------------------------------------------------
-- Multiplication Axioms
--------------------------------------------------------------------------------

-- Axiom 1
def mulNatZeroEqZero {P : Sort u} (T : Type v) 
  [IsNat P T] [LEq P T] [Mul T] [Zero T] [LIf P] [LForall P T] : P :=
  forall (a : T) => nat a -> a * 0 = 0

-- Axiom 2
def mulNatSuccEqAddMul {P : Sort u} (T : Type v) 
  [IsNat P T] [LEq P T] [Add T] [Mul T] [Succ T] [LIf P] [LAnd P] [LForall P T] : P := 
  forall (a b : T) => nat a /\ nat b -> a + S b = a + S (a * b)

--------------------------------------------------------------------------------
-- Inequality Axioms
--------------------------------------------------------------------------------

-- Axiom 1
def leIffAddNat 
  {P : Sort u} (T : Type v) 
  [IsNat P T]  [LE P T] [LEq P T] [Add T] 
  [LIf P] [LIff P] [LAnd P] [LForall P T] [LExists P T] : P :=
  forall (a b : T) => nat a /\ nat b -> (a <= b <-> exists c => nat c -> a + c = b)

-- Axiom 2
def strongNatInduction 
  {P : Sort u} (T : Type v) 
  [IsNat P T] [LE P T] [Zero T] [Succ T]
  [LIf P] [LAnd P] [LForall P T] [LForall P (T -> P)] : P := 
  forall (f : T -> P) => 
    f 0 -> 
    (forall (n k : T) => nat n /\ nat k -> (((k <= n) -> f n) -> f (S n))) ->
    (forall (n : T) => nat n -> f n)

end Gaea.Peano.Props
