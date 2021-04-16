import Gaea.Peano.Eq
import Gaea.Peano.Nat
import Gaea.Math.Notation



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
  (L : Logic P) (N : IsNat P T) (Q : SEq P T) (M : Mul T) (Z : Zero T)  :=
  (mulNatZeroEqZero : (a : T) -> (L |- nat a) -> (L |- a * 0 = 0))

def mulNatZeroEqZero {P : Sort u} {T : Type v} 
  {L : Logic P} [N : IsNat P T] [Q : SEq P T] [M : Mul T] [Z : Zero T] 
  [K : MulNatZeroEqZero L N Q M Z] {a : T} := K.mulNatZeroEqZero a

-- Axiom 2
-- a * S b = a + (a * b)

class MulNatSuccEqAddMul {P : Sort u} {T : Type v} 
  (L : Logic P) (N : IsNat P T) (Q : SEq P T) (M : Mul T) (A : Add T) (Su : Succ T) := 
  (mulNatSuccEqAddMul : (a b : T) -> (L |- nat a) -> (L |- nat b) -> 
    (L |- a * S b = a + (a * b)))

def mulNatSuccEqAddMul {P : Sort u} {T : Type v} 
  {L : Logic P} [N : IsNat P T] [Q : SEq P T] [M : Mul T] [A : Add T] [Su : Succ T]
  [K : MulNatSuccEqAddMul L N Q M A Su] {a b : T} := K.mulNatSuccEqAddMul a b

--------------------------------------------------------------------------------
-- Commmuted Axioms
--------------------------------------------------------------------------------

-- Axiom 1 Commuted
-- 0 * a = 0

class MulZeroNatEqZero {P : Sort u} {T : Type v} 
  (L : Logic P) (N : IsNat P T) (Q : SEq P T) (M : Mul T) (Z : Zero T)  :=
  (mulZeroNatEqZero : (a : T) -> (L |- nat a) -> (L |- 0 * a = 0))

def mulZeroNatEqZero {P : Sort u} {T : Type v} 
  {L : Logic P} [N : IsNat P T] [Q : SEq P T] [M : Mul T] [Z : Zero T] 
  [K : MulZeroNatEqZero L N Q M Z] {a : T} := K.mulZeroNatEqZero a

-- Axiom 2 Commuted
-- S a * b = b + (a * b)

class MulSuccNatEqAddMul {P : Sort u} {T : Type v} 
  (L : Logic P) (N : IsNat P T) (Q : SEq P T) (M : Mul T) (A : Add T) (Su : Succ T) := 
  (mulSuccNatEqAddMul : (a b : T) -> (L |- nat a) -> (L |- nat b) -> 
    (L |- S a * b = b + (a * b)))

def mulSuccNatEqAddMul {P : Sort u} {T : Type v} 
  {L : Logic P} [N : IsNat P T] [Q : SEq P T] [M : Mul T] [A : Add T] [Su : Succ T]
  [K : MulSuccNatEqAddMul L N Q M A Su] {a b : T} := K.mulSuccNatEqAddMul a b

--------------------------------------------------------------------------------
-- Special Cases
--------------------------------------------------------------------------------

-- 0 * 0 = 0

class MulZeroEqZero {P : Sort u} {T : Type v} 
  (L : Logic P) (Q : SEq P T) (M : Mul T) (Z : Zero T) :=
  (mulZeroEqZero : L |- 0 * 0 = (0 : T)) 

def mulZeroEqZero {P : Sort u} {T : Type v} 
  {L : Logic P} [Q : SEq P T] [M : Mul T] [Z : Zero T] 
  [K : MulZeroEqZero L Q M Z] := K.mulZeroEqZero

-- a * 1 = a

class MulNatOneEqNat {P : Sort u} {T : Type v} 
  (L : Logic P) (N : IsNat P T) (Q : SEq P T) (M : Mul T) (O : One T) :=
  (mulNatOneEqNat : (a : T) -> (L |- nat a) -> (L |- a * 1 = a))

def mulNatOneEqNat {P : Sort u} {T : Type v} 
  {L : Logic P} [N : IsNat P T] [Q : SEq P T] [M : Mul T] [O : One T]
  [K : MulNatOneEqNat L N Q M O] {a : T} := K.mulNatOneEqNat a

-- 1 * a = a

class MulOneNatEqNat {P : Sort u} {T : Type v} 
  (L : Logic P) (N : IsNat P T) (Q : SEq P T) (M : Mul T) (O : One T) :=
  (mulOneNatEqNat : (a : T) -> (L |- nat a) -> (L |- 1 * a = a))

def mulOneNatEqNat {P : Sort u} {T : Type v} 
  {L : Logic P} [N : IsNat P T] [Q : SEq P T] [M : Mul T] [O : One T]
  [K : MulOneNatEqNat L N Q M O] {a : T} := K.mulOneNatEqNat a

--------------------------------------------------------------------------------
-- Commutativity
--------------------------------------------------------------------------------

-- 0 * a = a * 0

class MulNatZeroComm {P : Sort u} {T : Type v} 
  (L : Logic P) (N : IsNat P T) (Q : SEq P T) (M : Mul T) (Z : Zero T) :=
  (mulNatZeroComm : (a : T) -> (L |- nat a) -> (L |- a * 0 = 0 * a))

def mulNatZeroComm {P : Sort u} {T : Type v} 
  {L : Logic P} [N : IsNat P T] [Q : SEq P T] [M : Mul T] [Z : Zero T]
  [K : MulNatZeroComm L N Q M Z] {a : T} := K.mulNatZeroComm a

-- a * b = b * a

class MulNatComm {P : Sort u} {T : Type v} 
  (L : Logic P) (N : IsNat P T) (Q : SEq P T) (M : Mul T) :=
  (mulNatComm : (a b : T) -> (L |- nat a) -> (L |- nat b) -> (L |- a * b = b * a))

instance iCommOverTOfMulNatCommOverT {P : Sort u} {T : Type v} 
  {L : Logic P} [N : IsNat P T] [Q : SEq P T] [M : Mul T] 
  [K : MulNatComm L N Q M] : CommOverT L Q.toFun N.isNat M.mul 
  := {commOverT := K.mulNatComm}

instance iMulNatCommOverOfCommOverT {P : Sort u} {T : Type v} 
  {L : Logic P} [N : IsNat P T] [Q : SEq P T] [M : Mul T] 
  [K : CommOverT L Q.toFun N.isNat M.mul] : MulNatComm L N Q M
  := {mulNatComm := K.commOverT}

def mulNatComm {P : Sort u} {T : Type v} 
  {L : Logic P} [N : IsNat P T] [Q : SEq P T] [M : Mul T]
  [K : MulNatComm L N Q M] {a b : T} := K.mulNatComm a b

--------------------------------------------------------------------------------
-- Associativity
-- (a * b) * c = a * (b * c)
--------------------------------------------------------------------------------

class MulNatAssoc {P : Sort u} {T : Type v}
  (L : Logic P) (N : IsNat P T) (Q : SEq P T) (M : Mul T) :=
  (mulNatAssoc :  (a b c : T) -> 
    (L |- nat a) -> (L |- nat b) -> (L |- nat c) ->
    (L |- (a * b) * c = a * (b * c)))

instance iLtrAssocOverTOfMulNatAssoc {P : Sort u} {T : Type v} 
  {L : Logic P} [N : IsNat P T] [Q : SEq P T] [M : Mul T] 
  [K : MulNatAssoc L N Q M] : LtrAssocOverT L Q.toFun N.isNat M.mul 
  := {ltrAssocOverT := K.mulNatAssoc}

instance iMulNatAssocOfLtrAssocOverT {P : Sort u} {T : Type v} 
  {L : Logic P} [N : IsNat P T] [Q : SEq P T] [M : Mul T] 
  [K : LtrAssocOverT L Q.toFun N.isNat M.mul] : MulNatAssoc L N Q M 
  := {mulNatAssoc := K.ltrAssocOverT}

def mulNatAssoc {P : Sort u} {T : Type v}
  {L : Logic P} [N : IsNat P T] [Q : SEq P T] [M : Mul T]
  [K : MulNatAssoc L N Q M] {a b c : T} := K.mulNatAssoc a b c

--------------------------------------------------------------------------------
-- Distributivity
--------------------------------------------------------------------------------

-- Left Distributive Over Addition
-- a * (b + c) = (a * b) + (a * c)

class MulNatAddEqAddMul {P : Sort u} {T : Type v} 
  (L : Logic P) (N : IsNat P T) (Q : SEq P T) (M : Mul T) (A : Add T) := 
  (mulNatAddEqAddMul : (a b c : T) -> 
    (L |- nat a) -> (L |- nat b) -> (L |- nat c) ->
    (L |- a * (b + c) = (a * b) + (a * c)))

def mulNatAddEqAddMul {P : Sort u} {T : Type v} 
  {L : Logic P} [N : IsNat P T] [Q : SEq P T] [M : Mul T] [A : Add T]
  [K : MulNatAddEqAddMul L N Q M A] {a b c : T} := K.mulNatAddEqAddMul a b c

-- Right Distributive Over Addition
-- (b + c) * a = (b * a) + (c * a)

class MulAddNatEqAddMul {P : Sort u} {T : Type v} 
  (L : Logic P) (N : IsNat P T) (Q : SEq P T) (M : Mul T) (A : Add T) := 
  (mulAddNatEqAddMul : (a b c : T) -> 
    (L |- nat a) -> (L |- nat b) -> (L |- nat c) ->
    (L |- (b + c) * a = (b * a) + (c * a)))

def mulAddNatEqAddMul {P : Sort u} {T : Type v} 
  {L : Logic P} [N : IsNat P T] [Q : SEq P T] [M : Mul T] [A : Add T]
  [K : MulAddNatEqAddMul L N Q M A] {a b c : T} := K.mulAddNatEqAddMul a b c

--------------------------------------------------------------------------------
-- Substitutivity
--------------------------------------------------------------------------------

-- (a = b) -> (c * a = c * b)

class EqNatMulNatLeft {P : Sort u} {T : Type v}
  (L : Logic P) (N : IsNat P T) (Q : SEq P T) (M : Mul T) :=
  (eqNatMulNatLeft : (a b c : T) -> 
    (L |- nat a) -> (L |- nat b) -> (L |- nat c) ->
    (L |- a = b) -> (L |- c * a = c * b))

instance iLeftReflTOfEqNatMulNatLeft {P : Sort u} {T : Type v} 
  {L : Logic P} [N : IsNat P T] [Q : SEq P T] [M : Mul T] 
  [K : EqNatMulNatLeft L N Q M] : LeftReflT L Q.toFun N.isNat M.mul 
  := {leftReflT := fun a b c Na Nb Nc => K.eqNatMulNatLeft b c a Nb Nc Na}

instance iEqNatMulNatLeftTOfLeftReflT {P : Sort u} {T : Type v} 
  {L : Logic P} [N : IsNat P T] [Q : SEq P T] [M : Mul T] 
  [K : LeftReflT L Q.toFun N.isNat M.mul] : EqNatMulNatLeft L N Q M
  := {eqNatMulNatLeft := fun a b c Na Nb Nc => K.leftReflT c a b Nc Na Nb}

def eqNatMulNatLeft {P : Sort u} {T : Type v}
  {L : Logic P} [N : IsNat P T] [Q : SEq P T] [M : Mul T]
  [K : EqNatMulNatLeft L N Q M] {a b c : T} := K.eqNatMulNatLeft a b c

def eqNatMulNatLeft' {P : Sort u} {T : Type v} {L : Logic P} 
  [N : IsNat P T] [Q : SEq P T] [M : Mul T] [K : EqNatMulNatLeft L N Q M] 
  {c a b : T} (Nc : L |- nat c) (Na : L |- nat a) (Nb : L|- nat b) 
  := K.eqNatMulNatLeft a b c Na Nb Nc

-- (a = b) -> (a * c = b * c)

class EqNatMulNatRight {P : Sort u} {T : Type v}
  (L : Logic P) (N : IsNat P T) (Q : SEq P T) (M : Mul T) :=
  (eqNatMulNatRight : (a b c : T) -> 
    (L |- nat a) -> (L |- nat b) -> (L |- nat c) ->
    (L |- a = b) -> (L |- a * c = b * c))

instance iRightReflTOfEqNatMulNatRight {P : Sort u} {T : Type v} 
  {L : Logic P} [N : IsNat P T] [Q : SEq P T] [M : Mul T] 
  [K : EqNatMulNatRight L N Q M] : RightReflT L Q.toFun N.isNat M.mul 
  := {rightReflT := fun a b c Na Nb Nc => K.eqNatMulNatRight b c a Nb Nc Na}

instance iEqNatMulNatRightOfRightReflT {P : Sort u} {T : Type v} 
  {L : Logic P} [N : IsNat P T] [Q : SEq P T] [M : Mul T] 
  [K : RightReflT L Q.toFun N.isNat M.mul] : EqNatMulNatRight L N Q M
  := {eqNatMulNatRight := fun a b c Na Nb Nc => K.rightReflT c a b Nc Na Nb}

def eqNatMulNatRight {P : Sort u} {T : Type v}
  {L : Logic P} [N : IsNat P T] [Q : SEq P T] [M : Mul T]
  [K : EqNatMulNatRight L N Q M] {a b c : T} := K.eqNatMulNatRight a b c

def eqNatMulNatRight' {P : Sort u} {T : Type v} {L : Logic P} 
  [N : IsNat P T] [Q : SEq P T] [M : Mul T] [K : EqNatMulNatRight L N Q M] 
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