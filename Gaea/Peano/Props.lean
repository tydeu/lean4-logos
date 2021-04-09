import Gaea.Math.Notation
import Gaea.Logic.Notation
import Gaea.Peano.Forall.Notation
import Gaea.Peano.Nat

universes u v

open Gaea.Math
open Gaea.Logic

namespace Gaea.Peano.Props

--------------------------------------------------------------------------------
-- Natural Axioms
--------------------------------------------------------------------------------

-- Axiom 1
def natZero {P : Sort u} (T : Type v) [IsNat P T] [Zero T] : P :=
  nat (0 : T)

-- Axiom 2
def eqNatRefl {P : Sort u} (T : Sort v) 
  [LEq P T] [ForallNat P T] : P :=
  forallNat (x : T) => x = x

-- Axiom 3
def eqNatSymm {P : Sort u} (T : Sort v) 
  [LEq P T] [Imp P] [ForallNat P T] : P :=
  forallNat (x y : T) => x = y -> y = x

-- Axiom 4
def eqNatTrans {P : Sort u} (T : Sort v) 
  [LEq P T] [Imp P] [Conj P] [ForallNat P T] : P :=
  forallNat (x y z : T) => x = y /\ y = z -> x = z

-- Axiom 5
def natEqNat {P : Sort u} (L : Logic P) (T : Sort v) 
  [IsNat P T] [LEq P T] [Imp P] [Conj P] [LForall P T] : P :=
  forall (a b : T) => nat b /\ a = b -> nat a

-- Axiom 6
def natSuccNat {P : Sort u} (T : Sort v) 
  [IsNat P T] [Succ T] [ForallNat P T] : P :=
  forallNat (n : T) => nat (S n)

-- Axiom 7
def eqNatIffEqSucc {P : Sort u} (T : Sort v) 
  [LEq P T] [Succ T] [LIff P] [ForallNat P T] : P :=
  forallNat (m n : T) => m = n <-> S m = S n

-- Axiom 7a
def eqNatToEqSucc {P : Sort u} (T : Sort v) 
  [LEq P T] [Succ T] [Imp P] [ForallNat P T] : P :=
  forallNat (m n : T) => m = n -> S m = S n

-- Axiom 7b
def eqSuccToEqNat {P : Sort u} (T : Sort v) 
  [LEq P T] [Succ T] [Imp P] [ForallNat P T] : P :=
  forallNat (m n : T) => S m = S n -> m = n

-- Axiom 8
def succNatEqZeroFalse {P : Sort u} (T : Type v) 
  [LEq P T] [LFalse P] [Zero T] [Succ T] [Imp P] [ForallNat P T] : P :=
  forallNat (m n : T) => S n = 0 -> false

-- Axiom 9
def natInduction 
  {P : Sort u} (T : Type v) 
  [Imp P] [LForall P (T -> P)]
  [ForallNat P T] [Zero T] [Succ T] : P := 
  forall (f : T -> P) => 
    f 0 -> 
    (forallNat (n : T) => f n -> f (S n)) ->
    (forallNat (n : T) => f n)

--------------------------------------------------------------------------------
-- Addition Axioms
--------------------------------------------------------------------------------

-- Axiom 1
def addNatZeroEqNat {P : Sort u} (T : Type v) 
  [LEq P T] [Add T] [Zero T] [ForallNat P T] : P :=
  forallNat (a : T) => a + 0 = a

-- Axiom 2
def addNatSuccEqSucc {P : Sort u} (T : Type v) 
  [LEq P T] [Add T] [Succ T] [ForallNat P T] : P := 
  forallNat (a b : T) => a + S b = S (a + b)

--------------------------------------------------------------------------------
-- Multiplication Axioms
--------------------------------------------------------------------------------

-- Axiom 1
def mulNatZeroEqZero {P : Sort u} (T : Type v) 
  [LEq P T] [Mul T] [Zero T] [ForallNat P T] : P :=
  forallNat (a : T) => a * 0 = 0

-- Axiom 2
def mulNatSuccEqAddMul {P : Sort u} (T : Type v) 
  [LEq P T] [Add T] [Mul T] [Succ T] [ForallNat P T] : P := 
  forallNat (a b : T) =>  a + S b = a + S (a * b)

--------------------------------------------------------------------------------
-- Inequality Axioms
--------------------------------------------------------------------------------

-- Axiom 1
def leIffAddNat 
  {P : Sort u} (T : Type v) 
  [IsNat P T] [LE P T] [LEq P T] [Add T] 
  [Imp P] [LIff P] [ForallNat P T] [LExists P T] : P :=
  forallNat (a b : T) => a <= b <-> exists c => nat c -> a + c = b

-- Axiom 2
def strongNatInduction 
  {P : Sort u} (T : Type v) 
  [Imp P] [Conj P] [LForall P (T -> P)] 
  [ForallNat P T] [LE P T] [Zero T] [Succ T] : P := 
  forall (f : T -> P) => 
    f 0 -> 
    (forallNat (n k : T) => (k <= n -> f n) -> f (S n)) ->
    (forallNat (n : T) => f n)

end Gaea.Peano.Props
