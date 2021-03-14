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

namespace NatZero
def nat0 {P : Sort u} {T : Type v} 
  {L : Logic P} [N : IsNat P T] [Z : Zero T] [C : NatZero L N Z] := C.natZero
end NatZero

export NatZero (natZero nat0)

-- Axiom 2
class EqNatRefl {P : Sort u} {T : Sort v} 
  (L : Logic P) (N : IsNat P T) (Eq : LEq P T) :=
  (eqNatRefl : (x : T) -> (L |- nat x) -> (L |- x = x))

export EqNatRefl (eqNatRefl)

-- Axiom 3
class EqNatSymm {P : Sort u} {T : Sort v} 
  (L : Logic P) (N : IsNat P T) (Eq : LEq P T) :=
  (eqNatSymm : (x y : T) -> (L |- nat x) -> (L |- nat y) ->
    (L |- x = y) -> (L |- y = x))

export EqNatSymm (eqNatSymm)

-- Axiom 4
class EqNatTrans {P : Sort u} {T : Sort v} 
  (L : Logic P) (N : IsNat P T) (Eq : LEq P T) :=
  (eqNatTrans : (x y z : T) -> (L |- nat x) -> (L |- nat y) -> (L |- nat z) -> 
    (L |- x = y) -> (L |- y = z) -> (L |- x = z))

export EqNatTrans (eqNatTrans)

-- Axiom 5
class NatEqNat {P : Sort u} {T : Sort v} 
  (L : Logic P) (N : IsNat P T) (Eq : LEq P T) :=
  (natEqNat : (a b : T) -> (L |- nat b) -> (L |- a = b) -> (L |- nat a))

namespace NatEqNat
def natEq {P : Sort u} {T : Sort v} 
{L : Logic P} [N : IsNat P T] [Eq : LEq P T] [C : NatEqNat L N Eq] 
{a b : T} : (L |- nat b) -> (L |- a = b) -> (L |- nat a) := C.natEqNat a b
end NatEqNat

export NatEqNat (natEqNat natEq)

-- Axiom 6
class NatSuccNat {P : Sort u} {T : Sort v} 
  (L : Logic P) (N : IsNat P T) (Su : Succ T) :=
  (natSuccNat : (n : T) -> (L |- nat n) -> (L |- nat (S n)))

namespace NatSuccNat
def natS {P : Sort u} {T : Sort v} 
{L : Logic P} [N : IsNat P T] [Su : Succ T] [C : NatSuccNat L N Su] 
{n : T} : (L |- nat n) -> (L |- nat (S n)) := C.natSuccNat n
end NatSuccNat

export NatSuccNat (natSuccNat natS)

-- Axiom 7a
class EqNatToEqSucc {P : Sort u} {T : Sort v} 
  (L : Logic P) (N : IsNat P T) (Eq : LEq P T) (Su : Succ T) :=
  (eqNatToEqSucc : (m n : T) -> (L |- nat m) -> (L |- nat n) -> 
    (L |- m = n) -> (L |- S m = S n))

export EqNatToEqSucc (eqNatToEqSucc)

-- Axiom 7b
class EqSuccToEqNat {P : Sort u} {T : Sort v} 
  (L : Logic P) (N : IsNat P T) (Eq : LEq P T) (Su : Succ T) :=
  (eqSuccToEqNat : (m n : T) -> (L |- nat m) -> (L |- nat n) -> 
    (L |- S m = S n) -> (L |- m = n))

export EqSuccToEqNat (eqSuccToEqNat)

-- Axiom 8
class SuccNatEqZeroFalse {P : Sort u} {T : Type v} 
  (L : Logic P) (N : IsNat P T) (Eq : LEq P T) (Z : Zero T) (Su : Succ T) [False P] :=
  (succNatEqZeroFalse : (m n : T) -> (L |- nat m) -> (L |- nat n) -> 
    (L |- S n = 0) -> (L |- false))

export SuccNatEqZeroFalse (succNatEqZeroFalse)

-- Axiom 9
-- Induction over predicates
class NatInduction {P : Sort u} {T : Type v} 
  (L : Logic P) (N : Nat P T) := 
  (natInduction : 
    (f : T -> P) -> (L |- f 0) -> 
    ((n : T) -> (L |- nat n) -> (L |- f n) -> (L |- f (S n))) ->
    ((n : T) -> (L |- nat n) -> (L |- f n)))

def natInduction {P : Sort u} {T : Type v} 
  {L : Logic P} [N : Nat P T] [I : NatInduction L N] := I.natInduction

-- Axiom 9 (Alt)
-- Induction over schemas
class NatInduction' {P : Sort u} {T : Type v} 
  (L : Logic P) (N : Nat P T) := 
  (natInduction' : (f : T -> Sort w) -> f 0 ->
    ((n : T) -> (L |- nat n) -> (f n -> f (S n))) ->
    ((n : T) -> (L |- nat n) -> f n))

def natInduction' {P : Sort u} {T : Type v} 
  (L : Logic P) [N : Nat P T] [I : NatInduction' L N] := I.natInduction'

--------------------------------------------------------------------------------
-- Addition Rules
--------------------------------------------------------------------------------

-- Axiom 1
class AddNatZeroEqNat {P : Sort u} {T : Type v} 
  (L : Logic P) (N : IsNat P T) (Eq : LEq P T) (A : Add T) (Z : Zero T) :=
  (addNatZeroEqNat : (a : T) -> (L |- nat a) -> (L |- a + 0 = a))

namespace AddNatZeroEqNat
def An0_eq_n {P : Sort u} {T : Type v} 
  {L : Logic P} [N : IsNat P T] [Eq : LEq P T] [A : Add T] [Z : Zero T] 
  [C : AddNatZeroEqNat L N Eq A Z] {a : T} := C.addNatZeroEqNat a
end AddNatZeroEqNat

export AddNatZeroEqNat (addNatZeroEqNat An0_eq_n)

-- Axiom 2
class AddNatSuccEqSucc {P : Sort u} {T : Type v} 
  (L : Logic P) (N : IsNat P T) (Eq : LEq P T) (A : Add T) (Su : Succ T) := 
  (addNatSuccEqSucc : (a b : T) -> (L |- nat a) -> (L |- nat b) -> 
    (L |- a + S b = S (a + b)))

namespace AddNatSuccEqSucc
def AmSn_eq_SAmn {P : Sort u} {T : Type v} 
  {L : Logic P} [N : IsNat P T] [Eq : LEq P T] [A : Add T] [Su : Succ T]
  [C : AddNatSuccEqSucc L N Eq A Su] {a b : T} := C.addNatSuccEqSucc a b
end AddNatSuccEqSucc

export AddNatSuccEqSucc (addNatSuccEqSucc AmSn_eq_SAmn)

--------------------------------------------------------------------------------
-- Multiplication Rules
--------------------------------------------------------------------------------

-- Axiom 1
class MulNatZeroEqZero {P : Sort u} {T : Type v} 
  (L : Logic P) (N : IsNat P T) (Eq : LEq P T) (M : Mul T) (Z : Zero T)  :=
  (mulNatZeroEqZero : (a : T) -> (L |- nat a) -> (L |- a * 0 = 0))

export MulNatZeroEqZero (mulNatZeroEqZero)

-- Axiom 2
class MulNatSuccEqAddMul {P : Sort u} {T : Type v} 
  (L : Logic P) (N : IsNat P T) (Eq : LEq P T) (M : Mul T) (A : Add T) (Su : Succ T) := 
  (mulNatSuccEqAddMul : (a b : T) -> (L |- nat a) -> (L |- nat b) -> 
    (L |- a + S b = a + S (a * b)))

export MulNatSuccEqAddMul (mulNatSuccEqAddMul)

end Gaea.Peano
