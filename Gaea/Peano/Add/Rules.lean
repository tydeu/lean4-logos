import Gaea.Logic
import Gaea.Syntax
import Gaea.Peano.Nat
import Gaea.Logic.Eq.Rules

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

instance {P : Sort u} {T : Type v} 
  {L : Logic P} [N : IsNat P T] [Q : LEq P T] [A : Add T] 
  [K : AddNatComm L N Q A] : MemComm L Q N.isNat A.add 
  := {memComm := K.addNatComm}

instance {P : Sort u} {T : Type v} 
  {L : Logic P} [N : IsNat P T] [Q : LEq P T] [A : Add T] 
  [K : MemComm L Q N.isNat A.add ] : AddNatComm L N Q A
  := {addNatComm := K.memComm}

def addNatComm {P : Sort u} {T : Type v} 
  {L : Logic P} [N : IsNat P T] [Q : LEq P T] [A : Add T]
  [C : AddNatComm L N Q A] {a b : T} := C.addNatComm a b

-- (a + b) + c = a + (b + c)

class AddNatAssoc {P : Sort u} {T : Type v}
  (L : Logic P) (N : IsNat P T) (Q : LEq P T) (A : Add T) :=
  (addNatAssoc :  (a b c : T) -> 
    (L |- nat a) -> (L |- nat b) -> (L |- nat c) ->
    (L |- (a + b) + c = a + (b + c)))

instance {P : Sort u} {T : Type v} 
  {L : Logic P} [N : IsNat P T] [Q : LEq P T] [A : Add T] 
  [K : AddNatAssoc L N Q A] : MemAssoc L Q N.isNat A.add 
  := {memAssoc := K.addNatAssoc}

instance {P : Sort u} {T : Type v} 
  {L : Logic P} [N : IsNat P T] [Q : LEq P T] [A : Add T] 
  [K : MemAssoc L Q N.isNat A.add] : AddNatAssoc L N Q A 
  := {addNatAssoc := K.memAssoc}

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

instance {P : Sort u} {T : Type v} 
  {L : Logic P} [N : IsNat P T] [Q : LEq P T] [A : Add T] 
  [K : EqNatAddNatLeft L N Q A] : EqMemMagLeft L Q N.isNat A.add 
  := {eqMemMagLeft := K.eqNatAddNatLeft}

instance {P : Sort u} {T : Type v} 
  {L : Logic P} [N : IsNat P T] [Q : LEq P T] [A : Add T] 
  [K : EqMemMagLeft L Q N.isNat A.add ] : EqNatAddNatLeft L N Q A
  := {eqNatAddNatLeft := K.eqMemMagLeft}

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

instance {P : Sort u} {T : Type v} 
  {L : Logic P} [N : IsNat P T] [Q : LEq P T] [A : Add T] 
  [K : EqNatAddNatRight L N Q A] : EqMemMagRight L Q N.isNat A.add 
  := {eqMemMagRight := K.eqNatAddNatRight}

instance {P : Sort u} {T : Type v} 
  {L : Logic P} [N : IsNat P T] [Q : LEq P T] [A : Add T] 
  [K : EqMemMagRight L Q N.isNat A.add ] : EqNatAddNatRight L N Q A
  := {eqNatAddNatRight := K.eqMemMagRight}

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
