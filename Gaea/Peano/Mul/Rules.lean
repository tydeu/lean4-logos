import Gaea.Logic.Eq
import Gaea.Logic.Logic
import Gaea.Math.Notation
import Gaea.Peano.Nat

universes u v w

open Gaea.Math
open Gaea.Logic

namespace Gaea.Peano

--------------------------------------------------------------------------------
-- Axioms
--------------------------------------------------------------------------------

-- Axiom 1
-- a * 0 = 0

class MulNatZeroEqZero {P : Sort u} {T : Type v} 
  (L : Logic P) (N : IsNat P T) (Q : LEq P T) (M : Mul T) (Z : Zero T)  :=
  (mulNatZeroEqZero : (a : T) -> (L |- nat a) -> (L |- a * 0 = 0))

def mulNatZeroEqZero {P : Sort u} {T : Type v} 
  {L : Logic P} [N : IsNat P T] [Q : LEq P T] [M : Mul T] [Z : Zero T] 
  [K : MulNatZeroEqZero L N Q M Z] {a : T} := K.mulNatZeroEqZero a

-- Axiom 2
-- a * S b = a + (a * b)

class MulNatSuccEqAddMul {P : Sort u} {T : Type v} 
  (L : Logic P) (N : IsNat P T) (Q : LEq P T) (M : Mul T) (A : Add T) (Su : Succ T) := 
  (mulNatSuccEqAddMul : (a b : T) -> (L |- nat a) -> (L |- nat b) -> 
    (L |- a * S b = a + (a * b)))

def mulNatSuccEqAddMul {P : Sort u} {T : Type v} 
  {L : Logic P} [N : IsNat P T] [Q : LEq P T] [M : Mul T] [A : Add T] [Su : Succ T]
  [K : MulNatSuccEqAddMul L N Q M A Su] {a b : T} := K.mulNatSuccEqAddMul a b

--------------------------------------------------------------------------------
-- Commmuted Axioms
--------------------------------------------------------------------------------

-- Axiom 1 Commuted
-- 0 * a = 0

class MulZeroNatEqZero {P : Sort u} {T : Type v} 
  (L : Logic P) (N : IsNat P T) (Q : LEq P T) (M : Mul T) (Z : Zero T)  :=
  (mulZeroNatEqZero : (a : T) -> (L |- nat a) -> (L |- 0 * a = 0))

def mulZeroNatEqZero {P : Sort u} {T : Type v} 
  {L : Logic P} [N : IsNat P T] [Q : LEq P T] [M : Mul T] [Z : Zero T] 
  [K : MulZeroNatEqZero L N Q M Z] {a : T} := K.mulZeroNatEqZero a

-- Axiom 2 Commuted
-- S a * b = b + (a * b)

class MulSuccNatEqAddMul {P : Sort u} {T : Type v} 
  (L : Logic P) (N : IsNat P T) (Q : LEq P T) (M : Mul T) (A : Add T) (Su : Succ T) := 
  (mulSuccNatEqAddMul : (a b : T) -> (L |- nat a) -> (L |- nat b) -> 
    (L |- S a * b = b + (a * b)))

def mulSuccNatEqAddMul {P : Sort u} {T : Type v} 
  {L : Logic P} [N : IsNat P T] [Q : LEq P T] [M : Mul T] [A : Add T] [Su : Succ T]
  [K : MulSuccNatEqAddMul L N Q M A Su] {a b : T} := K.mulSuccNatEqAddMul a b

--------------------------------------------------------------------------------
-- Special Cases
--------------------------------------------------------------------------------

-- 0 * 0 = 0

class MulZeroEqZero {P : Sort u} {T : Type v} 
  (L : Logic P) (Q : LEq P T) (M : Mul T) (Z : Zero T) :=
  (mulZeroEqZero : L |- 0 * 0 = (0 : T)) 

def mulZeroEqZero {P : Sort u} {T : Type v} 
  {L : Logic P} [Q : LEq P T] [M : Mul T] [Z : Zero T] 
  [K : MulZeroEqZero L Q M Z] := K.mulZeroEqZero

-- a * 1 = a

class MulNatOneEqNat {P : Sort u} {T : Type v} 
  (L : Logic P) (N : IsNat P T) (Q : LEq P T) (M : Mul T) (O : One T) :=
  (mulNatOneEqNat : (a : T) -> (L |- nat a) -> (L |- a * 1 = a))

def mulNatOneEqNat {P : Sort u} {T : Type v} 
  {L : Logic P} [N : IsNat P T] [Q : LEq P T] [M : Mul T] [O : One T]
  [K : MulNatOneEqNat L N Q M O] {a : T} := K.mulNatOneEqNat a

-- 1 * a = a

class MulOneNatEqNat {P : Sort u} {T : Type v} 
  (L : Logic P) (N : IsNat P T) (Q : LEq P T) (M : Mul T) (O : One T) :=
  (mulOneNatEqNat : (a : T) -> (L |- nat a) -> (L |- 1 * a = a))

def mulOneNatEqNat {P : Sort u} {T : Type v} 
  {L : Logic P} [N : IsNat P T] [Q : LEq P T] [M : Mul T] [O : One T]
  [K : MulOneNatEqNat L N Q M O] {a : T} := K.mulOneNatEqNat a

--------------------------------------------------------------------------------
-- Commutativity
--------------------------------------------------------------------------------

-- 0 * a = a * 0

class MulNatZeroComm {P : Sort u} {T : Type v} 
  (L : Logic P) (N : IsNat P T) (Q : LEq P T) (M : Mul T) (Z : Zero T) :=
  (mulNatZeroComm : (a : T) -> (L |- nat a) -> (L |- a * 0 = 0 * a))

def mulNatZeroComm {P : Sort u} {T : Type v} 
  {L : Logic P} [N : IsNat P T] [Q : LEq P T] [M : Mul T] [Z : Zero T]
  [K : MulNatZeroComm L N Q M Z] {a : T} := K.mulNatZeroComm a

-- a * b = b * a

class MulNatComm {P : Sort u} {T : Type v} 
  (L : Logic P) (N : IsNat P T) (Q : LEq P T) (M : Mul T) :=
  (mulNatComm : (a b : T) -> (L |- nat a) -> (L |- nat b) -> (L |- a * b = b * a))

instance i_MulNatComm_to_MemComm {P : Sort u} {T : Type v} 
  {L : Logic P} [N : IsNat P T] [Q : LEq P T] [M : Mul T] 
  [K : MulNatComm L N Q M] : MemComm L Q N.isNat M.mul 
  := {memComm := K.mulNatComm}

instance i_MemComm_to_MulNatComm {P : Sort u} {T : Type v} 
  {L : Logic P} [N : IsNat P T] [Q : LEq P T] [M : Mul T] 
  [K : MemComm L Q N.isNat M.mul ] : MulNatComm L N Q M
  := {mulNatComm := K.memComm}

def mulNatComm {P : Sort u} {T : Type v} 
  {L : Logic P} [N : IsNat P T] [Q : LEq P T] [M : Mul T]
  [K : MulNatComm L N Q M] {a b : T} := K.mulNatComm a b

--------------------------------------------------------------------------------
-- Associativity
-- (a * b) * c = a * (b * c)
--------------------------------------------------------------------------------

class MulNatAssoc {P : Sort u} {T : Type v}
  (L : Logic P) (N : IsNat P T) (Q : LEq P T) (M : Mul T) :=
  (mulNatAssoc :  (a b c : T) -> 
    (L |- nat a) -> (L |- nat b) -> (L |- nat c) ->
    (L |- (a * b) * c = a * (b * c)))

instance i_MulNatAssoc_to_MemAssoc {P : Sort u} {T : Type v} 
  {L : Logic P} [N : IsNat P T] [Q : LEq P T] [M : Mul T] 
  [K : MulNatAssoc L N Q M] : MemAssoc L Q N.isNat M.mul 
  := {memAssoc := K.mulNatAssoc}

instance i_MemAssoc_to_MulNatAssoc {P : Sort u} {T : Type v} 
  {L : Logic P} [N : IsNat P T] [Q : LEq P T] [M : Mul T] 
  [K : MemAssoc L Q N.isNat M.mul] : MulNatAssoc L N Q M 
  := {mulNatAssoc := K.memAssoc}

def mulNatAssoc {P : Sort u} {T : Type v}
  {L : Logic P} [N : IsNat P T] [Q : LEq P T] [M : Mul T]
  [K : MulNatAssoc L N Q M] {a b c : T} := K.mulNatAssoc a b c

--------------------------------------------------------------------------------
-- Distributivity
--------------------------------------------------------------------------------

-- Left Distributive Over Addition
-- a * (b + c) = (a * b) + (a * c)

class MulNatAddEqAddMul {P : Sort u} {T : Type v} 
  (L : Logic P) (N : IsNat P T) (Q : LEq P T) (M : Mul T) (A : Add T) := 
  (mulNatAddEqAddMul : (a b c : T) -> 
    (L |- nat a) -> (L |- nat b) -> (L |- nat c) ->
    (L |- a * (b + c) = (a * b) + (a * c)))

def mulNatAddEqAddMul {P : Sort u} {T : Type v} 
  {L : Logic P} [N : IsNat P T] [Q : LEq P T] [M : Mul T] [A : Add T]
  [K : MulNatAddEqAddMul L N Q M A] {a b c : T} := K.mulNatAddEqAddMul a b c

-- Right Distributive Over Addition
-- (b + c) * a = (b * a) + (c * a)

class MulAddNatEqAddMul {P : Sort u} {T : Type v} 
  (L : Logic P) (N : IsNat P T) (Q : LEq P T) (M : Mul T) (A : Add T) := 
  (mulAddNatEqAddMul : (a b c : T) -> 
    (L |- nat a) -> (L |- nat b) -> (L |- nat c) ->
    (L |- (b + c) * a = (b * a) + (c * a)))

def mulAddNatEqAddMul {P : Sort u} {T : Type v} 
  {L : Logic P} [N : IsNat P T] [Q : LEq P T] [M : Mul T] [A : Add T]
  [K : MulAddNatEqAddMul L N Q M A] {a b c : T} := K.mulAddNatEqAddMul a b c

--------------------------------------------------------------------------------
-- Substitutivity
--------------------------------------------------------------------------------

-- (a = b) -> (c * a = c * b)

class EqNatMulNatLeft {P : Sort u} {T : Type v}
  (L : Logic P) (N : IsNat P T) (Q : LEq P T) (M : Mul T) :=
  (eqNatMulNatLeft : (a b c : T) -> 
    (L |- nat a) -> (L |- nat b) -> (L |- nat c) ->
    (L |- a = b) -> (L |- c * a = c * b))

instance i_EqNatMulNatLeft_to_EqMemMagLeft {P : Sort u} {T : Type v} 
  {L : Logic P} [N : IsNat P T] [Q : LEq P T] [M : Mul T] 
  [K : EqNatMulNatLeft L N Q M] : EqMemMagLeft L Q N.isNat M.mul 
  := {eqMemMagLeft := K.eqNatMulNatLeft}

instance i_EqMemMagLeft_to_EqNatMulNatLeft  {P : Sort u} {T : Type v} 
  {L : Logic P} [N : IsNat P T] [Q : LEq P T] [M : Mul T] 
  [K : EqMemMagLeft L Q N.isNat M.mul ] : EqNatMulNatLeft L N Q M
  := {eqNatMulNatLeft := K.eqMemMagLeft}

def eqNatMulNatLeft {P : Sort u} {T : Type v}
  {L : Logic P} [N : IsNat P T] [Q : LEq P T] [M : Mul T]
  [K : EqNatMulNatLeft L N Q M] {a b c : T} := K.eqNatMulNatLeft a b c

def eqNatMulNatLeft' {P : Sort u} {T : Type v} {L : Logic P} 
  [N : IsNat P T] [Q : LEq P T] [M : Mul T] [K : EqNatMulNatLeft L N Q M] 
  {c a b : T} (Nc : L |- nat c) (Na : L |- nat a) (Nb : L|- nat b) 
  := K.eqNatMulNatLeft a b c Na Nb Nc

-- (a = b) -> (a * c = b * c)

class EqNatMulNatRight {P : Sort u} {T : Type v}
  (L : Logic P) (N : IsNat P T) (Q : LEq P T) (M : Mul T) :=
  (eqNatMulNatRight : (a b c : T) -> 
    (L |- nat a) -> (L |- nat b) -> (L |- nat c) ->
    (L |- a = b) -> (L |- a * c = b * c))

instance i_EqNatMulNatRight_to_EqMemMagRight {P : Sort u} {T : Type v} 
  {L : Logic P} [N : IsNat P T] [Q : LEq P T] [M : Mul T] 
  [K : EqNatMulNatRight L N Q M] : EqMemMagRight L Q N.isNat M.mul 
  := {eqMemMagRight := K.eqNatMulNatRight}

instance i_EqMemMagRight_to_EqNatMulNatRight  {P : Sort u} {T : Type v} 
  {L : Logic P} [N : IsNat P T] [Q : LEq P T] [M : Mul T] 
  [K : EqMemMagRight L Q N.isNat M.mul] : EqNatMulNatRight L N Q M
  := {eqNatMulNatRight := K.eqMemMagRight}

def eqNatMulNatRight {P : Sort u} {T : Type v}
  {L : Logic P} [N : IsNat P T] [Q : LEq P T] [M : Mul T]
  [K : EqNatMulNatRight L N Q M] {a b c : T} := K.eqNatMulNatRight a b c

def eqNatMulNatRight' {P : Sort u} {T : Type v} {L : Logic P} 
  [N : IsNat P T] [Q : LEq P T] [M : Mul T] [K : EqNatMulNatRight L N Q M] 
  {c a b : T} (Nc : L |- nat c) (Na : L |- nat a) (Nb : L|- nat b) 
  := K.eqNatMulNatRight a b c Na Nb Nc

--------------------------------------------------------------------------------
-- Closure
--------------------------------------------------------------------------------

-- nat (0 * 0)

class NatMulZero {P : Sort u} {T : Type v} 
  (L : Logic P) (N : IsNat P T) (M : Mul T) (Z : Zero T) :=
  (natMulZero : L |- nat (0 * 0 : T))

def natMulZero {P : Sort u} {T : Type v} 
  {L : Logic P} [N : IsNat P T] [M : Mul T] [Z : Zero T]
  [K : NatMulZero L N M Z] := K.natMulZero

-- nat (a * 0)

class NatMulNatZero {P : Sort u} {T : Type v} 
  (L : Logic P) (N : IsNat P T) (M : Mul T) (Z : Zero T) :=
  (natMulNatZero : (a : T) -> (L |- nat a) -> (L |- nat (a * 0)))

def natMulNatZero {P : Sort u} {T : Type v} 
  {L : Logic P} [N : IsNat P T] [M : Mul T] [Z : Zero T]
  [K : NatMulNatZero L N M Z] {a : T} := K.natMulNatZero a

-- nat (0 * a)

class NatMulZeroNat {P : Sort u} {T : Type v} 
  (L : Logic P) (N : IsNat P T) (M : Mul T) (Z : Zero T) :=
  (natMulZeroNat : (a : T) -> (L |- nat a) -> (L |- nat (0 * a)))

def natMulZeroNat {P : Sort u} {T : Type v} 
  {L : Logic P} [N : IsNat P T] [M : Mul T] [Z : Zero T]
  [K : NatMulZeroNat L N M Z] {a : T} := K.natMulZeroNat a 

-- nat (a * b)

class NatMulNat {P : Sort u} {T : Type v}
  (L : Logic P) (N : IsNat P T) (M : Mul T) :=
  (natMulNat : (a b : T) -> (L |- nat a) -> (L |- nat b) -> (L |- nat (a * b)))

def natMulNat {P : Sort u} {T : Type v}
  {L : Logic P} [N : IsNat P T] [M : Mul T] [K : NatMulNat L N M]
  {a b : T} := K.natMulNat a b

def natMul {P : Sort u} {T : Type v}
  {L : Logic P} [N : IsNat P T] [M : Mul T] [K : NatMulNat L N M]
  {a b : T} := K.natMulNat a b

end Gaea.Peano