import Gaea.Logic
import Gaea.Peano.Nat

import Gaea.Syntax.Math
import Gaea.Syntax.Logic
import Gaea.Syntax.Notation
import Gaea.Logic.Notation

open Gaea.Logic
open Gaea.Syntax

namespace Gaea.Peano.Props

universes u v

-- Axiom 1
def natZero {P : Sort u} (N : Type u) [Nat P N] [Zero N] : P :=
  nat (0 : N)

-- Axiom 2
def eqNatRefl {P : Sort u} (N : Sort v) 
  [LForall P N] [LIf P] [LEq P N] [Nat P N] : P :=
  forall (x : N) => nat x -> x = x

-- Axiom 3
def eqNatSymm {P : Sort u} (N : Sort v) 
  [LForall P N] [LIf P] [LAnd P] [LEq P N] [Nat P N]: P :=
  forall (x y : N) => nat x /\ nat y -> (x = y -> y = x)

-- Axiom 4
def eqNatTrans {P : Sort u} (N : Sort v) 
  [LForall P N] [LIf P] [LAnd P] [LEq P N] [Nat P N] : P :=
  forall (x y z : N) => nat x /\ nat y /\ nat z -> (x = y /\ y = z -> x = z)

-- Axiom 5
def natEq {P : Sort u} (L : Logic P) (N : Sort v) 
  [LForall P N] [LIf P] [LEq P N] [Nat P N] : P :=
  forall (a b : N) => nat b -> (a = b) -> nat a

-- Axiom 6
def natSuccNat {P : Sort u} (N : Sort v) 
  [LForall P N] [LIf P] [Nat P N] [Succ N] : P :=
  forall (n : N) => nat n -> nat (S n)

-- Axiom 7a
def succNatSubst {P : Sort u} (N : Sort v) 
  [LForall P N] [LIf P] [LAnd P] [LEq P N] [Nat P N] [Succ N] : P  :=
  forall (m n : N) => nat m /\ nat n -> (m = n -> S m = S n)

-- Axiom 7b
def succNatInj {P : Sort u} (N : Sort v) 
  [LForall P N] [LIf P] [LAnd P] [LEq P N] [Nat P N] [Succ N] : P  :=
  forall (m n : N) => nat m /\ nat n -> (S m = S n -> m = n)

-- Axiom 8
def succNatEqZeroFalse {P : Sort u} (N : Type v) 
  [LForall P N] [LIf P] [LAnd P] [LEq P N] [Nat P N] [Zero N] [Succ N] [False P] : P  :=
  forall (m n : N) => nat m /\ nat n -> (S n = 0 -> false)

-- Axiom 9
def natInduction 
  {P : Sort u} (N : Type v) [Nat P N] 
  [LForall P (N -> P)] [LForall P N] [LIf P] [LAnd P] [LEq P N] 
  [Nat P N] [Zero N] [Succ N] : P := 
  forall (f : N -> P) => 
    f 0 -> (forall (n : N) => nat n -> (f n -> f (S n))) ->
      forall (n : N) => nat n -> f n

end Gaea.Peano.Props
