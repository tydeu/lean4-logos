import Gaea.Math.Notation
import Gaea.Logic.Prop.Syntax
import Gaea.Logic.Quant.Syntax
import Gaea.Logic.Eq.Syntax
import Gaea.Peano.Forall.Syntax
import Gaea.Peano.Nat

open Gaea.Math
open Gaea.Logic
open Gaea.Logic.Notation
open Gaea.Peano.Notation

namespace Gaea.Peano.Props

universes u v
variable 
  {P : Sort u} (T : Sort v)
  [Iff : SIff P] [Arr : LArr P] [Cj : Conj P]
  [Fa : SForall P T] [Fa2 : SForall P (T -> P)] [FaN : SForallNat P T]
  [X : SExists P T]
  [F : Falsum P]
  [Q : SEq P T] [Le : SLessEq P T]
  [N : IsNat P T] [Z : Zero T] [S : Succ T]
  [A : SAdd T] [M : SMul T]

--------------------------------------------------------------------------------
-- Natural Axioms
--------------------------------------------------------------------------------

-- Axiom 1
def natZero : P := 
  nat (0 : T)

-- Axiom 2
def eqNatRefl : P :=
  forallNat (x : T) => x = x

-- Axiom 3
def eqNatSymm : P :=
  forallNat (x y : T) => x = y -> y = x

-- Axiom 4
def eqNatTrans : P :=
  forallNat (x y z : T) => x = y /\ y = z -> x = z

-- Axiom 5
def natEqNat : P :=
  forall (a b : T) => nat b /\ a = b -> nat a

-- Axiom 6
def natSuccNat : P :=
  forallNat (n : T) => nat (S n)

-- Axiom 7
def eqNatIffEqSucc : P :=
  forallNat (m n : T) => m = n <-> S m = S n

-- Axiom 7a
def eqNatToEqSucc : P :=
  forallNat (m n : T) => m = n -> S m = S n

-- Axiom 7b
def eqSuccToEqNat : P :=
  forallNat (m n : T) => S m = S n -> m = n

-- Axiom 8
def succNatEqZeroFalse : P :=
  forallNat (m n : T) => S n = 0 -> falsum

-- Axiom 9
def natInduction : P := 
  forall (f : T -> P) => 
    f 0 -> 
    (forallNat (n : T) => f n -> f (S n)) ->
    (forallNat (n : T) => f n)

--------------------------------------------------------------------------------
-- Addition Axioms
--------------------------------------------------------------------------------

-- Axiom 1
def addNatZeroEqNat : P :=
  forallNat (a : T) => a + 0 = a

-- Axiom 2
def addNatSuccEqSucc : P := 
  forallNat (a b : T) => a + S b = S (a + b)

--------------------------------------------------------------------------------
-- Multiplication Axioms
--------------------------------------------------------------------------------

-- Axiom 1
def mulNatZeroEqZero : P :=
  forallNat (a : T) => a * 0 = 0

-- Axiom 2
def mulNatSuccEqAddMul : P := 
  forallNat (a b : T) => a + S b = a + S (a * b)

--------------------------------------------------------------------------------
-- Inequality Axioms
--------------------------------------------------------------------------------

-- Axiom 1
def leNatIffAddNatEqNat : P :=
  forallNat (a b : T) => (a <= b) <-> (exists c => nat c -> a + c = b)

-- Axiom 2
def strongNatInduction : P := 
  forall (f : T -> P) => 
    f 0 -> 
    (forallNat (n k : T) => ((k <= n) -> f n) -> f (S n)) ->
    (forallNat (n : T) => f n)
