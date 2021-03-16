import Gaea.Logic
import Gaea.Syntax
import Gaea.Peano.Nat

universes u v w

open Gaea.Logic
open Gaea.Syntax

namespace Gaea.Peano

-- 0 + 0 = 0

class AddZeroEqZero {P : Sort u} {T : Type v} 
  (L : Logic P) (Q : LEq P T) (A : Add T) (Z : Zero T) :=
  (addZeroEqZero : L |- 0 + 0 = (0 : T)) 

def addZeroEqZero {P : Sort u} {T : Type v} 
  {L : Logic P} [Q : LEq P T] [A : Add T] [Z : Zero T] 
  [C : AddZeroEqZero L Q A Z] := C.addZeroEqZero

-- 0 + a = a + 0

class AddNatZeroComm {P : Sort u} {T : Type v} 
  (L : Logic P) (N : IsNat P T) (Q : LEq P T) (A : Add T) (Z : Zero T) :=
  (addNatZeroComm : (a : T) -> (L |- nat a) -> (L |- a + 0 = 0 + a))

def addNatZeroComm {P : Sort u} {T : Type v} 
  {L : Logic P} [N : IsNat P T] [Q : LEq P T] [A : Add T] [Z : Zero T]
  [C : AddNatZeroComm L N Q A Z] {a : T} := C.addNatZeroComm a

-- a + b = b + a

class AddNatComm {P : Sort u} {T : Type v} 
  (L : Logic P) (N : IsNat P T) (Q : LEq P T) (A : Add T) :=
  (addNatComm : (a b : T) -> (L |- nat a) -> (L |- nat b) -> (L |- a + b = b + a))

def addNatComm {P : Sort u} {T : Type v} 
  {L : Logic P} [N : IsNat P T] [Q : LEq P T] [A : Add T]
  [C : AddNatComm L N Q A] {a b : T} := C.addNatComm a b

-- (a + b) + c = a + (b + c)

class AddNatAssoc {P : Sort u} {T : Type v}
  (L : Logic P) (N : IsNat P T) (Q : LEq P T) (A : Add T) :=
  (addNatAssoc :  (a b c : T) -> 
    (L |- nat a) -> (L |- nat b) -> (L |- nat c) ->
    (L |- (a + b) + c = a + (b + c)))

def addNatAssoc {P : Sort u} {T : Type v}
  {L : Logic P} [N : IsNat P T] [Q : LEq P T] [A : Add T]
  [C : AddNatAssoc L N Q A] {a b c : T} := C.addNatAssoc a b c

--------------------------------------------------------------------------------
-- Substitutivity
--------------------------------------------------------------------------------

-- (a = b) -> (c + a = c + b)

class EqNatAddNatLeft {P : Sort u} {T : Type v}
  (L : Logic P) (N : IsNat P T) (Q : LEq P T) (A : Add T) :=
  (eqNatAddNatLeft : (a b c : T) -> 
    (L |- nat a) -> (L |- nat b) -> (L |- nat c) ->
    (L |- a = b) -> (L |- c + a = c + b))

def eqNatAddNatLeft {P : Sort u} {T : Type v}
  {L : Logic P} [N : IsNat P T] [Q : LEq P T] [A : Add T]
  [C : EqNatAddNatLeft L N Q A] {a b c : T} := C.eqNatAddNatLeft a b c

def eqNatAddNatLeft' {P : Sort u} {T : Type v} {L : Logic P} 
  [N : IsNat P T] [Q : LEq P T] [A : Add T] [C : EqNatAddNatLeft L N Q A] 
  {c a b : T} (Nc : L |- nat c) (Na : L |- nat a) (Nb : L|- nat b) 
  := C.eqNatAddNatLeft a b c Na Nb Nc

-- (a = b) -> (a + c = b + c)

class EqNatAddNatRight {P : Sort u} {T : Type v}
  (L : Logic P) (N : IsNat P T) (Q : LEq P T) (A : Add T) :=
  (eqNatAddNatRight : (a b c : T) -> 
    (L |- nat a) -> (L |- nat b) -> (L |- nat c) ->
    (L |- a = b) -> (L |- a + c = b + c))

def eqNatAddNatRight {P : Sort u} {T : Type v}
  {L : Logic P} [N : IsNat P T] [Q : LEq P T] [A : Add T]
  [C : EqNatAddNatRight L N Q A] {a b c : T} := C.eqNatAddNatRight a b c

def eqNatAddNatRight' {P : Sort u} {T : Type v} {L : Logic P} 
  [N : IsNat P T] [Q : LEq P T] [A : Add T] [C : EqNatAddNatRight L N Q A] 
  {c a b : T} (Nc : L |- nat c) (Na : L |- nat a) (Nb : L|- nat b) 
  := C.eqNatAddNatRight a b c Na Nb Nc

--------------------------------------------------------------------------------
-- Closure
--------------------------------------------------------------------------------

-- nat (a + 0)

class NatAddNatZero {P : Sort u} {T : Type v} 
  (L : Logic P) (N : IsNat P T) (A : Add T) (Z : Zero T) :=
  (natAddNatZero : (a : T) -> (L |- nat a) -> (L |- nat (a + 0)))

def natAddNatZero {P : Sort u} {T : Type v} 
  {L : Logic P} [N : IsNat P T] [A : Add T] [Z : Zero T]
  [C : NatAddNatZero L N A Z] {a : T} := C.natAddNatZero a

-- nat (0 + a)

class NatAddZeroNat {P : Sort u} {T : Type v} 
  (L : Logic P) (N : IsNat P T) (A : Add T) (Z : Zero T) :=
  (natAddZeroNat : (a : T) -> (L |- nat a) -> (L |- nat (0 + a)))

def natAddZeroNat {P : Sort u} {T : Type v} 
  {L : Logic P} [N : IsNat P T] [A : Add T] [Z : Zero T]
  [C : NatAddZeroNat L N A Z] {a : T} := C.natAddZeroNat a 

-- nat (a + b)

class NatAddNat {P : Sort u} {T : Type v}
  (L : Logic P) (N : IsNat P T) (A : Add T) :=
  (natAddNat : (a b : T) -> (L |- nat a) -> (L |- nat b) -> (L |- nat (a + b)))

def natAddNat {P : Sort u} {T : Type v}
  {L : Logic P} [N : IsNat P T] [A : Add T] [C : NatAddNat L N A]
  {a b : T} := C.natAddNat a b

def natAdd {P : Sort u} {T : Type v}
  {L : Logic P} [N : IsNat P T] [A : Add T] [C : NatAddNat L N A]
  {a b : T} := C.natAddNat a b


end Gaea.Peano
