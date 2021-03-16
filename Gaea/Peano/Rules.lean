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
  {L : Logic P} [N : IsNat P T] [Z : Zero T] [C : NatZero L N Z] := C.natZero

def nat0 {P : Sort u} {T : Type v} 
  {L : Logic P} [N : IsNat P T] [Z : Zero T] [C : NatZero L N Z] := C.natZero

-- Axiom 2
class EqNatRefl {P : Sort u} {T : Sort v} 
  (L : Logic P) (N : IsNat P T) (Q : LEq P T) :=
  (eqNatRefl : (x : T) -> (L |- nat x) -> (L |- x = x))

def eqNatRefl {P : Sort u} {T : Sort v} 
  {L : Logic P} [N : IsNat P T] [Q : LEq P T] [C : EqNatRefl L N Q]
  {x : T} := C.eqNatRefl x

-- Axiom 3
class EqNatSymm {P : Sort u} {T : Sort v} 
  (L : Logic P) (N : IsNat P T) (Q : LEq P T) :=
  (eqNatSymm : (x y : T) -> (L |- nat x) -> (L |- nat y) ->
    (L |- x = y) -> (L |- y = x))

def eqNatSymm {P : Sort u} {T : Sort v} 
  {L : Logic P} [N : IsNat P T] [Q : LEq P T] [C : EqNatSymm L N Q]
  {x y : T} := C.eqNatSymm x y

-- Axiom 4
class EqNatTrans {P : Sort u} {T : Sort v} 
  (L : Logic P) (N : IsNat P T) (Q : LEq P T) :=
  (eqNatTrans : (x y z : T) -> (L |- nat x) -> (L |- nat y) -> (L |- nat z) -> 
    (L |- x = y) -> (L |- y = z) -> (L |- x = z))

def eqNatTrans {P : Sort u} {T : Sort v} 
  {L : Logic P} [N : IsNat P T] [Q : LEq P T] [C : EqNatTrans L N Q]
  {x y z : T} := C.eqNatTrans x y z

def eqNatTrans' {P : Sort u} {T : Sort v} 
  {L : Logic P} [N : IsNat P T] [Q : LEq P T] [C : EqNatTrans L N Q]
  {y x z : T} (Ny : L |- nat y) (Nx : L |- nat x) (Nz : L |- nat z)  
  := C.eqNatTrans x y z Nx Ny Nz

-- Axiom 5
class NatEqNat {P : Sort u} {T : Sort v} 
  (L : Logic P) (N : IsNat P T) (Q : LEq P T) :=
  (natEqNat : (a b : T) -> (L |- nat b) -> (L |- a = b) -> (L |- nat a))

def natEqNat {P : Sort u} {T : Sort v} 
  {L : Logic P} [N : IsNat P T] [Q : LEq P T] [C : NatEqNat L N Q] 
  {a b : T} := C.natEqNat a b

def natEq {P : Sort u} {T : Sort v} 
  {L : Logic P} [N : IsNat P T] [Q : LEq P T] [C : NatEqNat L N Q] 
  {a b : T} := C.natEqNat a b

-- Axiom 6
class NatSuccNat {P : Sort u} {T : Sort v} 
  (L : Logic P) (N : IsNat P T) (Su : Succ T) :=
  (natSuccNat : (n : T) -> (L |- nat n) -> (L |- nat (S n)))

def natSuccNat {P : Sort u} {T : Sort v} 
{L : Logic P} [N : IsNat P T] [Su : Succ T] [C : NatSuccNat L N Su] 
{n : T} := C.natSuccNat n

def natS {P : Sort u} {T : Sort v} 
{L : Logic P} [N : IsNat P T] [Su : Succ T] [C : NatSuccNat L N Su] 
{n : T} := C.natSuccNat n

-- Axiom 7a
class EqNatToEqSucc {P : Sort u} {T : Sort v} 
  (L : Logic P) (N : IsNat P T) (Q : LEq P T) (Su : Succ T) :=
  (eqNatToEqSucc : (m n : T) -> (L |- nat m) -> (L |- nat n) -> 
    (L |- m = n) -> (L |- S m = S n))

def eqNatToEqSucc {P : Sort u} {T : Sort v} 
  {L : Logic P} [N : IsNat P T] [Q : LEq P T] [Su : Succ T]
  [C : EqNatToEqSucc L N Q Su] {m n : T} := C.eqNatToEqSucc m n

-- Axiom 7b
class EqSuccToEqNat {P : Sort u} {T : Sort v} 
  (L : Logic P) (N : IsNat P T) (Q : LEq P T) (Su : Succ T) :=
  (eqSuccToEqNat : (m n : T) -> (L |- nat m) -> (L |- nat n) -> 
    (L |- S m = S n) -> (L |- m = n))

def eqSuccToEqNat {P : Sort u} {T : Sort v} 
  {L : Logic P} [N : IsNat P T] [Q : LEq P T] [Su : Succ T]
  [C : EqSuccToEqNat L N Q Su] {m n : T} := C.eqSuccToEqNat

-- Axiom 8
class SuccNatEqZeroFalse {P : Sort u} {T : Type v} 
  (L : Logic P) (N : PNat P T) (Q : LEq P T) (F : LFalse P) :=
  (succNatEqZeroFalse : (m n : T) -> (L |- nat m) -> (L |- nat n) -> 
    (L |- S n = 0) -> (L |- false))

def succNatEqZeroFalse {P : Sort u} {T : Type v} 
  {L : Logic P} [N : PNat P T] [Q : LEq P T] [F : LFalse P]
  [C : SuccNatEqZeroFalse L N Q F] {m n : T} := C.succNatEqZeroFalse m n

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
  [C : AddNatZeroEqNat L N Q A Z] {a : T} := C.addNatZeroEqNat a

-- Axiom 2
class AddNatSuccEqSucc {P : Sort u} {T : Type v} 
  (L : Logic P) (N : IsNat P T) (Q : LEq P T) (A : Add T) (Su : Succ T) := 
  (addNatSuccEqSucc : (a b : T) -> (L |- nat a) -> (L |- nat b) -> 
    (L |- a + S b = S (a + b)))

def addNatSuccEqSucc {P : Sort u} {T : Type v} 
  {L : Logic P} [N : IsNat P T] [Q : LEq P T] [A : Add T] [Su : Succ T]
  [C : AddNatSuccEqSucc L N Q A Su] {a b : T} := C.addNatSuccEqSucc a b

-- Axiom 1 Commuted
class AddZeroNatEqNat {P : Sort u} {T : Type v} 
  (L : Logic P) (N : IsNat P T) (Q : LEq P T) (A : Add T) (Z : Zero T) :=
  (addZeroNatEqNat : (a : T) -> (L |- nat a) -> (L |- 0 + a = a))

def addZeroNatEqNat {P : Sort u} {T : Type v} 
  {L : Logic P} [N : IsNat P T] [Q : LEq P T] [A : Add T] [Z : Zero T] 
  [C : AddZeroNatEqNat L N Q A Z] {a : T} := C.addZeroNatEqNat a

-- Axiom 2 Commuted
class AddSuccNatEqSucc {P : Sort u} {T : Type v} 
  (L : Logic P) (N : IsNat P T) (Q : LEq P T) (A : Add T) (Su : Succ T) := 
  (addSuccNatEqSucc : (a b : T) -> (L |- nat a) -> (L |- nat b) -> 
    (L |- S a + b = S (a + b)))

def addSuccNatEqSucc {P : Sort u} {T : Type v} 
  {L : Logic P} [N : IsNat P T] [Q : LEq P T] [A : Add T] [Su : Succ T]
  [C : AddSuccNatEqSucc L N Q A Su] {a b : T} := C.addSuccNatEqSucc a b

--------------------------------------------------------------------------------
-- Multiplication Rules
--------------------------------------------------------------------------------

-- Axiom 1
class MulNatZeroEqZero {P : Sort u} {T : Type v} 
  (L : Logic P) (N : IsNat P T) (Q : LEq P T) (M : Mul T) (Z : Zero T)  :=
  (mulNatZeroEqZero : (a : T) -> (L |- nat a) -> (L |- a * 0 = 0))

def mulNatZeroEqZero {P : Sort u} {T : Type v} 
  {L : Logic P} [N : IsNat P T] [Q : LEq P T] [M : Mul T] [Z : Zero T] 
  [C : MulNatZeroEqZero L N Q M Z] {a : T} := C.mulNatZeroEqZero a

-- Axiom 2
class MulNatSuccEqAddMul {P : Sort u} {T : Type v} 
  (L : Logic P) (N : IsNat P T) (Q : LEq P T) (M : Mul T) (A : Add T) (Su : Succ T) := 
  (mulNatSuccEqAddMul : (a b : T) -> (L |- nat a) -> (L |- nat b) -> 
    (L |- a + S b = a + S (a * b)))

def mulNatSuccEqAddMul {P : Sort u} {T : Type v} 
  {L : Logic P} [N : IsNat P T] [Q : LEq P T] [M : Mul T] [A : Add T] [Su : Succ T]
  [C : MulNatSuccEqAddMul L N Q M A Su] {a b : T} := C.mulNatSuccEqAddMul a b

-- Axiom 1 Commuted
class MulZeroNatEqZero {P : Sort u} {T : Type v} 
  (L : Logic P) (N : IsNat P T) (Q : LEq P T) (M : Mul T) (Z : Zero T)  :=
  (mulZeroNatEqZero : (a : T) -> (L |- nat a) -> (L |- 0 * a = 0))

def mulZeroNatEqZero {P : Sort u} {T : Type v} 
  {L : Logic P} [N : IsNat P T] [Q : LEq P T] [M : Mul T] [Z : Zero T] 
  [C : MulZeroNatEqZero L N Q M Z] {a : T} := C.mulZeroNatEqZero a

-- Axiom 2 Commuted
class MulSuccNatEqAddMul {P : Sort u} {T : Type v} 
  (L : Logic P) (N : IsNat P T) (Q : LEq P T) (M : Mul T) (A : Add T) (Su : Succ T) := 
  (mulSuccNatEqAddMul : (a b : T) -> (L |- nat a) -> (L |- nat b) -> 
    (L |- S a + b = a + S (a * b)))

def mulSuccNatEqAddMul {P : Sort u} {T : Type v} 
  {L : Logic P} [N : IsNat P T] [Q : LEq P T] [M : Mul T] [A : Add T] [Su : Succ T]
  [C : MulSuccNatEqAddMul L N Q M A Su] {a b : T} := C.mulSuccNatEqAddMul a b

end Gaea.Peano
