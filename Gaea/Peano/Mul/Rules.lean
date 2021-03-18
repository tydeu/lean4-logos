import Gaea.Logic
import Gaea.Syntax
import Gaea.Peano.Nat

universes u v w

open Gaea.Logic
open Gaea.Syntax

namespace Gaea.Peano
--------------------------------------------------------------------------------
-- Special Cases
--------------------------------------------------------------------------------

-- 0 * 0 = 0

class MulZeroEqZero {P : Sort u} {T : Type v} 
  (L : Logic P) (Q : LEq P T) (M : Mul T) (Z : Zero T) :=
  (mulZeroEqZero : L |- 0 * 0 = (0 : T)) 

def mulZeroEqZero {P : Sort u} {T : Type v} 
  {L : Logic P} [Q : LEq P T] [M : Mul T] [Z : Zero T] 
  [C : MulZeroEqZero L Q M Z] := C.mulZeroEqZero

-- a * 1 = a

class MulNatOneEqNat {P : Sort u} {T : Type v} 
  (L : Logic P) (N : IsNat P T) (Q : LEq P T) (M : Mul T) (N1 : One T) :=
  (mulNatOneEqNat : (a : T) -> (L |- nat a) -> (L |- a * 1 = a))

def mulNatOneEqNat {P : Sort u} {T : Type v} 
  {L : Logic P} [N : IsNat P T] [Q : LEq P T] [M : Mul T] [N1 : One T]
  [C : MulNatOneEqNat L N Q M N1] {a : T} := C.mulNatOneEqNat a

-- 1 * a = a

class MulOneNatEqNat {P : Sort u} {T : Type v} 
  (L : Logic P) (N : IsNat P T) (Q : LEq P T) (M : Mul T) (N1 : One T) :=
  (mulOneNatEqNat : (a : T) -> (L |- nat a) -> (L |- 1 * a = a))

def mulOneNatEqNat {P : Sort u} {T : Type v} 
  {L : Logic P} [N : IsNat P T] [Q : LEq P T] [M : Mul T] [N1 : One T]
  [C : MulOneNatEqNat L N Q M N1] {a : T} := C.mulOneNatEqNat a

--------------------------------------------------------------------------------
-- Commutativity
--------------------------------------------------------------------------------

-- 0 * a = a * 0

class MulNatZeroComm {P : Sort u} {T : Type v} 
  (L : Logic P) (N : IsNat P T) (Q : LEq P T) (M : Mul T) (Z : Zero T) :=
  (mulNatZeroComm : (a : T) -> (L |- nat a) -> (L |- a * 0 = 0 * a))

def mulNatZeroComm {P : Sort u} {T : Type v} 
  {L : Logic P} [N : IsNat P T] [Q : LEq P T] [M : Mul T] [Z : Zero T]
  [C : MulNatZeroComm L N Q M Z] {a : T} := C.mulNatZeroComm a

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
  [C : MulNatComm L N Q M] {a b : T} := C.mulNatComm a b

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
  [C : MulNatAssoc L N Q M] {a b c : T} := C.mulNatAssoc a b c

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
  [C : EqNatMulNatLeft L N Q M] {a b c : T} := C.eqNatMulNatLeft a b c

def eqNatMulNatLeft' {P : Sort u} {T : Type v} {L : Logic P} 
  [N : IsNat P T] [Q : LEq P T] [M : Mul T] [C : EqNatMulNatLeft L N Q M] 
  {c a b : T} (Nc : L |- nat c) (Na : L |- nat a) (Nb : L|- nat b) 
  := C.eqNatMulNatLeft a b c Na Nb Nc

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
  [C : EqNatMulNatRight L N Q M] {a b c : T} := C.eqNatMulNatRight a b c

def eqNatMulNatRight' {P : Sort u} {T : Type v} {L : Logic P} 
  [N : IsNat P T] [Q : LEq P T] [M : Mul T] [C : EqNatMulNatRight L N Q M] 
  {c a b : T} (Nc : L |- nat c) (Na : L |- nat a) (Nb : L|- nat b) 
  := C.eqNatMulNatRight a b c Na Nb Nc

--------------------------------------------------------------------------------
-- Closure
--------------------------------------------------------------------------------

-- nat (a * 0)

class NatMulNatZero {P : Sort u} {T : Type v} 
  (L : Logic P) (N : IsNat P T) (M : Mul T) (Z : Zero T) :=
  (natMulNatZero : (a : T) -> (L |- nat a) -> (L |- nat (a * 0)))

def natMulNatZero {P : Sort u} {T : Type v} 
  {L : Logic P} [N : IsNat P T] [M : Mul T] [Z : Zero T]
  [C : NatMulNatZero L N M Z] {a : T} := C.natMulNatZero a

-- nat (0 * a)

class NatMulZeroNat {P : Sort u} {T : Type v} 
  (L : Logic P) (N : IsNat P T) (M : Mul T) (Z : Zero T) :=
  (natMulZeroNat : (a : T) -> (L |- nat a) -> (L |- nat (0 * a)))

def natMulZeroNat {P : Sort u} {T : Type v} 
  {L : Logic P} [N : IsNat P T] [M : Mul T] [Z : Zero T]
  [C : NatMulZeroNat L N M Z] {a : T} := C.natMulZeroNat a 

-- nat (a * b)

class NatMulNat {P : Sort u} {T : Type v}
  (L : Logic P) (N : IsNat P T) (M : Mul T) :=
  (natMulNat : (a b : T) -> (L |- nat a) -> (L |- nat b) -> (L |- nat (a * b)))

def natMulNat {P : Sort u} {T : Type v}
  {L : Logic P} [N : IsNat P T] [M : Mul T] [C : NatMulNat L N M]
  {a b : T} := C.natMulNat a b

def natMul {P : Sort u} {T : Type v}
  {L : Logic P} [N : IsNat P T] [M : Mul T] [C : NatMulNat L N M]
  {a b : T} := C.natMulNat a b

end Gaea.Peano