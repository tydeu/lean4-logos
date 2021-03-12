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

-- Axiom 1
def natZero {P : Sort u} (T : Type v) [Nat P T] [Zero T] : P :=
  nat (0 : T)

-- Axiom 2
def eqNatRefl {P : Sort u} (T : Sort v) 
  [LForall P T] [LIf P] [LEq P T] [Nat P T] : P :=
  forall (x : T) => nat x -> x = x

-- Axiom 3
def eqNatSymm {P : Sort u} (T : Sort v) 
  [LForall P T] [LIf P] [LAnd P] [LEq P T] [Nat P T] : P :=
  forall (x y : T) => nat x /\ nat y -> (x = y -> y = x)

-- Axiom 4
def eqNatTrans {P : Sort u} (T : Sort v) 
  [LForall P T] [LIf P] [LAnd P] [LEq P T] [Nat P T] : P :=
  forall (x y z : T) => nat x /\ nat y /\ nat z -> (x = y /\ y = z -> x = z)

-- Axiom 5
def natEq {P : Sort u} (L : Logic P) (T : Sort v) 
  [LForall P T] [LIf P] [LAnd P] [LEq P T] [Nat P T] : P :=
  forall (a b : T) => nat b /\ a = b -> nat a

-- Axiom 6
def natSuccNat {P : Sort u} (T : Sort v) 
  [LForall P T] [LIf P] [Nat P T] [Succ T] : P :=
  forall (n : T) => nat n -> nat (S n)

-- Axiom 7
def succNatOto {P : Sort u} (T : Sort v) 
  [LForall P T] [LIf P] [LAnd P] [LIff P] [LEq P T] [Nat P T] [Succ T] : P :=
  forall (m n : T) => nat m /\ nat n -> (m = n <-> S m = S n)

-- Axiom 7a
def succNatSubst {P : Sort u} (T : Sort v) 
  [LForall P T] [LIf P] [LAnd P] [LEq P T] [Nat P T] [Succ T] : P :=
  forall (m n : T) => nat m /\ nat n -> (m = n -> S m = S n)

-- Axiom 7b
def succNatInj {P : Sort u} (T : Sort v) 
  [LForall P T] [LIf P] [LAnd P] [LEq P T] [Nat P T] [Succ T] : P :=
  forall (m n : T) => nat m /\ nat n -> (S m = S n -> m = n)

-- Axiom 8
def succNatEqZeroFalse {P : Sort u} (T : Type v) 
  [LForall P T] [LIf P] [LAnd P] [LEq P T] [False P] [Nat P T] [Zero T] [Succ T] : P :=
  forall (m n : T) => nat m /\ nat n -> (S n = 0 -> false)

-- Axiom 9
def natInduction {P : Sort u} (T : Type v) 
  [LForall P (T -> P)] [LForall P T] [LIf P] [LAnd P] [LEq P T] 
  [Nat P T] [Zero T] [Succ T] : P := 
  forall (f : T -> P) => 
    f 0 -> (forall (n : T) => nat n -> (f n -> f (S n))) ->
      forall (n : T) => nat n -> f n

end Gaea.Peano.Props
