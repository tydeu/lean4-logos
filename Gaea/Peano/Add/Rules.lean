import Gaea.Peano.Eq
import Gaea.Peano.Nat
import Gaea.Math.Notation

universes u v

open Gaea.Math
open Gaea.Logic

namespace Gaea.Peano

--------------------------------------------------------------------------------
-- Axioms
--------------------------------------------------------------------------------

-- Axiom 1
class AddNatZeroEqNat {P : Sort u} {T : Sort v} 
  (L : Logic P) (N : IsNat P T) (Q : SEq P T) (A : SAdd T) (Z : Zero T) :=
  (addNatZeroEqNat : (a : T) -> (L |- nat a) -> (L |- a + 0 = a))

def addNatZeroEqNat {P : Sort u} {T : Sort v} 
  {L : Logic P} [N : IsNat P T] [Q : SEq P T] [A : SAdd T] [Z : Zero T] 
  [K : AddNatZeroEqNat L N Q A Z] {a : T} := K.addNatZeroEqNat a

-- Axiom 2
class AddNatSuccEqSucc {P : Sort u} {T : Sort v} 
  (L : Logic P) (N : IsNat P T) (Q : SEq P T) (A : SAdd T) (S : Succ T) := 
  (addNatSuccEqSucc : (a b : T) -> (L |- nat a) -> (L |- nat b) -> 
    (L |- a + S b = S (a + b)))

def addNatSuccEqSucc {P : Sort u} {T : Sort v} 
  {L : Logic P} [N : IsNat P T] [Q : SEq P T] [A : SAdd T] [S : Succ T]
  [K : AddNatSuccEqSucc L N Q A S] {a b : T} := K.addNatSuccEqSucc a b

--------------------------------------------------------------------------------
-- Commuted Axioms
--------------------------------------------------------------------------------

-- Axiom 1 Commuted
class AddZeroNatEqNat {P : Sort u} {T : Sort v} 
  (L : Logic P) (N : IsNat P T) (Q : SEq P T) (A : SAdd T) (Z : Zero T) :=
  (addZeroNatEqNat : (a : T) -> (L |- nat a) -> (L |- 0 + a = a))

def addZeroNatEqNat {P : Sort u} {T : Sort v} 
  {L : Logic P} [N : IsNat P T] [Q : SEq P T] [A : SAdd T] [Z : Zero T] 
  [K : AddZeroNatEqNat L N Q A Z] {a : T} := K.addZeroNatEqNat a

-- Axiom 2 Commuted
class AddSuccNatEqSucc {P : Sort u} {T : Sort v} 
  (L : Logic P) (N : IsNat P T) (Q : SEq P T) (A : SAdd T) (S : Succ T) := 
  (addSuccNatEqSucc : (a b : T) -> (L |- nat a) -> (L |- nat b) -> 
    (L |- S a + b = S (a + b)))

def addSuccNatEqSucc {P : Sort u} {T : Sort v} 
  {L : Logic P} [N : IsNat P T] [Q : SEq P T] [A : SAdd T] [S : Succ T]
  [K : AddSuccNatEqSucc L N Q A S] {a b : T} := K.addSuccNatEqSucc a b

--------------------------------------------------------------------------------
-- Special Cases
--------------------------------------------------------------------------------

-- 0 + 0 = 0

class AddZeroEqZero {P : Sort u} {T : Sort v} 
  (L : Logic P) (Q : SEq P T) (A : SAdd T) (Z : Zero T) :=
  (addZeroEqZero : L |- 0 + 0 = (0 : T)) 

def addZeroEqZero {P : Sort u} {T : Sort v} 
  {L : Logic P} [Q : SEq P T] [A : SAdd T] [Z : Zero T] 
  [C : AddZeroEqZero L Q A Z] := C.addZeroEqZero

-- a + 1 = S a

class AddNatOneEqSucc {P : Sort u} {T : Sort v} 
  (L : Logic P) (N : IsNat P T) (Q : SEq P T) (A : SAdd T) (O : One T) (S : Succ T) :=
  (addNatOneEqSucc : (a : T) -> (L |- nat a) -> (L |- a + 1 = S a))

def addNatOneEqSucc {P : Sort u} {T : Sort v} 
  {L : Logic P} [N : IsNat P T] [Q : SEq P T] [A : SAdd T] [O : One T] [S : Succ T]
  [C : AddNatOneEqSucc L N Q A O S] {a : T} := C.addNatOneEqSucc a

-- 1 + a = S a

class AddOneNatEqSucc {P : Sort u} {T : Sort v} 
  (L : Logic P) (N : IsNat P T) (Q : SEq P T) (A : SAdd T) (O : One T) (S : Succ T) :=
  (addOneNatEqSucc : (a : T) -> (L |- nat a) -> (L |- 1 + a = S a))

def addOneNatEqSucc {P : Sort u} {T : Sort v} 
  {L : Logic P} [N : IsNat P T] [Q : SEq P T] [A : SAdd T] [O : One T] [S : Succ T]
  [C : AddOneNatEqSucc L N Q A O S] {a : T} := C.addOneNatEqSucc a

--------------------------------------------------------------------------------
-- Commutativity
--------------------------------------------------------------------------------

-- 0 + a = a + 0

class AddNatZeroComm {P : Sort u} {T : Sort v} 
  (L : Logic P) (N : IsNat P T) (Q : SEq P T) (A : SAdd T) (Z : Zero T) :=
  (addNatZeroComm : (a : T) -> (L |- nat a) -> (L |- a + 0 = 0 + a))

def addNatZeroComm {P : Sort u} {T : Sort v} 
  {L : Logic P} [N : IsNat P T] [Q : SEq P T] [A : SAdd T] [Z : Zero T]
  [C : AddNatZeroComm L N Q A Z] {a : T} := C.addNatZeroComm a

-- a + b = b + a

class AddNatComm {P : Sort u} {T : Sort v} 
  (L : Logic P) (N : IsNat P T) (Q : SEq P T) (A : SAdd T) :=
  (addNatComm : (a b : T) -> (L |- nat a) -> (L |- nat b) -> (L |- a + b = b + a))

instance iCommOverTOfAddNatComm {P : Sort u} {T : Sort v} 
  {L : Logic P} [N : IsNat P T] [Q : SEq P T] [A : SAdd T] 
  [K : AddNatComm L N Q A] : CommOverT L Q.toFun N.isNat A.toFun 
  := {commOverT := K.addNatComm}

instance iAddNatCommOverTOfComm {P : Sort u} {T : Sort v} 
  {L : Logic P} [N : IsNat P T] [Q : SEq P T] [A : SAdd T] 
  [K : CommOverT L Q.toFun N.isNat A.toFun ] : AddNatComm L N Q A
  := {addNatComm := K.commOverT}

def addNatComm {P : Sort u} {T : Sort v} 
  {L : Logic P} [N : IsNat P T] [Q : SEq P T] [A : SAdd T]
  [C : AddNatComm L N Q A] {a b : T} := C.addNatComm a b

--------------------------------------------------------------------------------
-- Associativity
--------------------------------------------------------------------------------

-- (a + b) + c = a + (b + c)

class AddNatAssoc {P : Sort u} {T : Sort v}
  (L : Logic P) (N : IsNat P T) (Q : SEq P T) (A : SAdd T) :=
  (addNatAssoc :  (a b c : T) -> 
    (L |- nat a) -> (L |- nat b) -> (L |- nat c) ->
    (L |- (a + b) + c = a + (b + c)))

instance iLtrAssocOverTOfAddNatAssoc {P : Sort u} {T : Sort v} 
  {L : Logic P} [N : IsNat P T] [Q : SEq P T] [A : SAdd T] 
  [K : AddNatAssoc L N Q A] : LtrAssocOverT L Q.toFun N.isNat A.toFun 
  := {ltrAssocOverT := K.addNatAssoc}

instance iAddNatAssocOfLtrAssocOverT {P : Sort u} {T : Sort v} 
  {L : Logic P} [N : IsNat P T] [Q : SEq P T] [A : SAdd T] 
  [K : LtrAssocOverT L Q.toFun N.isNat A.toFun] : AddNatAssoc L N Q A 
  := {addNatAssoc := K.ltrAssocOverT}

def addNatAssoc {P : Sort u} {T : Sort v}
  {L : Logic P} [N : IsNat P T] [Q : SEq P T] [A : SAdd T]
  [C : AddNatAssoc L N Q A] {a b c : T} := C.addNatAssoc a b c

-- a + (b + c) = (a + b) + c 

class AddNatAssocRev {P : Sort u} {T : Sort v}
  (L : Logic P) (N : IsNat P T) (Q : SEq P T) (A : SAdd T) :=
  (addNatAssocRev :  (a b c : T) -> 
    (L |- nat a) -> (L |- nat b) -> (L |- nat c) ->
    (L |- a + (b + c) = (a + b) + c))

def addNatAssocRev {P : Sort u} {T : Sort v}
  {L : Logic P} [N : IsNat P T] [Q : SEq P T] [A : SAdd T]
  [C : AddNatAssocRev L N Q A] {a b c : T} := C.addNatAssocRev a b c

--------------------------------------------------------------------------------
-- Substitutivity
--------------------------------------------------------------------------------

-- (a = b) -> (c + a = c + b)

class EqNatAddNatLeft {P : Sort u} {T : Sort v}
  (L : Logic P) (N : IsNat P T) (Q : SEq P T) (A : SAdd T) :=
  (eqNatAddNatLeft : (a b c : T) -> 
    (L |- nat a) -> (L |- nat b) -> (L |- nat c) ->
    (L |- a = b) -> (L |- c + a = c + b))

instance iLeftReflTOfEqNatAddNatLeft {P : Sort u} {T : Sort v} 
  {L : Logic P} [N : IsNat P T] [Q : SEq P T] [A : SAdd T] 
  [K : EqNatAddNatLeft L N Q A] : LeftReflT L Q.toFun N.isNat A.toFun 
  := {leftReflT := fun a b c Na Nb Nc => K.eqNatAddNatLeft b c a Nb Nc Na}

instance iEqNatAddNatLeftTOfLeftReflT {P : Sort u} {T : Sort v} 
  {L : Logic P} [N : IsNat P T] [Q : SEq P T] [A : SAdd T] 
  [K : LeftReflT L Q.toFun N.isNat A.toFun] : EqNatAddNatLeft L N Q A
  := {eqNatAddNatLeft := fun a b c Na Nb Nc => K.leftReflT c a b Nc Na Nb}

def eqNatAddNatLeft {P : Sort u} {T : Sort v}
  {L : Logic P} [N : IsNat P T] [Q : SEq P T] [A : SAdd T]
  [C : EqNatAddNatLeft L N Q A] {a b c : T} := C.eqNatAddNatLeft a b c

def eqNatAddNatLeft' {P : Sort u} {T : Sort v} {L : Logic P} 
  [N : IsNat P T] [Q : SEq P T] [A : SAdd T] [C : EqNatAddNatLeft L N Q A] 
  {c a b : T} (Nc : L |- nat c) (Na : L |- nat a) (Nb : L|- nat b) 
  := C.eqNatAddNatLeft a b c Na Nb Nc

-- (a = b) -> (a + c = b + c)

class EqNatAddNatRight {P : Sort u} {T : Sort v}
  (L : Logic P) (N : IsNat P T) (Q : SEq P T) (A : SAdd T) :=
  (eqNatAddNatRight : (a b c : T) -> 
    (L |- nat a) -> (L |- nat b) -> (L |- nat c) ->
    (L |- a = b) -> (L |- a + c = b + c))

instance iRightReflTOfEqNatAddNatRight {P : Sort u} {T : Sort v} 
  {L : Logic P} [N : IsNat P T] [Q : SEq P T] [A : SAdd T] 
  [K : EqNatAddNatRight L N Q A] : RightReflT L Q.toFun N.isNat A.toFun 
  := {rightReflT := fun a b c Na Nb Nc => K.eqNatAddNatRight b c a Nb Nc Na}

instance iEqNatAddNatRightOfRightReflT {P : Sort u} {T : Sort v} 
  {L : Logic P} [N : IsNat P T] [Q : SEq P T] [A : SAdd T] 
  [K : RightReflT L Q.toFun N.isNat A.toFun] : EqNatAddNatRight L N Q A
  := {eqNatAddNatRight := fun a b c Na Nb Nc => K.rightReflT c a b Nc Na Nb}

def eqNatAddNatRight {P : Sort u} {T : Sort v}
  {L : Logic P} [N : IsNat P T] [Q : SEq P T] [A : SAdd T]
  [C : EqNatAddNatRight L N Q A] {a b c : T} := C.eqNatAddNatRight a b c

def eqNatAddNatRight' {P : Sort u} {T : Sort v} {L : Logic P} 
  [N : IsNat P T] [Q : SEq P T] [A : SAdd T] [C : EqNatAddNatRight L N Q A] 
  {c a b : T} (Nc : L |- nat c) (Na : L |- nat a) (Nb : L|- nat b) 
  := C.eqNatAddNatRight a b c Na Nb Nc

--------------------------------------------------------------------------------
-- Closure
--------------------------------------------------------------------------------

-- nat (0 + 0)

class NatAddZero {P : Sort u} {T : Sort v} 
  (L : Logic P) (N : IsNat P T) (A : SAdd T) (Z : Zero T) :=
  (natAddZero : L |- nat (0 + 0 : T))

def natAddZero {P : Sort u} {T : Sort v} 
  {L : Logic P} [N : IsNat P T] [A : SAdd T] [Z : Zero T]
  [C : NatAddZero L N A Z] := C.natAddZero

-- nat (a + 0)

class NatAddNatZero {P : Sort u} {T : Sort v} 
  (L : Logic P) (N : IsNat P T) (A : SAdd T) (Z : Zero T) :=
  (natAddNatZero : (a : T) -> (L |- nat a) -> (L |- nat (a + 0)))

def natAddNatZero {P : Sort u} {T : Sort v} 
  {L : Logic P} [N : IsNat P T] [A : SAdd T] [Z : Zero T]
  [C : NatAddNatZero L N A Z] {a : T} := C.natAddNatZero a

-- nat (0 + a)

class NatAddZeroNat {P : Sort u} {T : Sort v} 
  (L : Logic P) (N : IsNat P T) (A : SAdd T) (Z : Zero T) :=
  (natAddZeroNat : (a : T) -> (L |- nat a) -> (L |- nat (0 + a)))

def natAddZeroNat {P : Sort u} {T : Sort v} 
  {L : Logic P} [N : IsNat P T] [A : SAdd T] [Z : Zero T]
  [C : NatAddZeroNat L N A Z] {a : T} := C.natAddZeroNat a 

-- nat (a + b)

class NatAddNat {P : Sort u} {T : Sort v}
  (L : Logic P) (N : IsNat P T) (A : SAdd T) :=
  (natAddNat : (a b : T) -> (L |- nat a) -> (L |- nat b) -> (L |- nat (a + b)))

def natAddNat {P : Sort u} {T : Sort v}
  {L : Logic P} [N : IsNat P T] [A : SAdd T] [C : NatAddNat L N A]
  {a b : T} := C.natAddNat a b

def natAdd {P : Sort u} {T : Sort v}
  {L : Logic P} [N : IsNat P T] [A : SAdd T] [C : NatAddNat L N A]
  {a b : T} := C.natAddNat a b

end Gaea.Peano
