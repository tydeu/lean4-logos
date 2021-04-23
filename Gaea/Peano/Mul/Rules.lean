import Gaea.Peano.Eq
import Gaea.Peano.Nat
import Gaea.Math.Notation

universes u v
variable {P : Sort u} {T : Sort v}

open Gaea.Notation
namespace Gaea.Peano

--------------------------------------------------------------------------------
-- Axioms
--------------------------------------------------------------------------------

-- Axiom 1
-- a * 0 = 0

class MulNatZeroEqZero (L : Logic P) 
  (N : IsNat P T) (Q : SEq P T) (M : SMul T) (Z : Zero T)  :=
  toFun : (a : T) -> (L |- nat a) -> (L |- a * 0 = 0)

abbrev mulNatZeroEqZero {L : Logic P} 
  [N : IsNat P T] [Q : SEq P T] [M : SMul T] [Z : Zero T] 
  [K : MulNatZeroEqZero L N Q M Z] {a} := K.toFun a

-- Axiom 2
-- a * S b = a + (a * b)

class MulNatSuccEqAddMul (L : Logic P) 
  (N : IsNat P T) (Q : SEq P T) (M : SMul T) (A : SAdd T) (S : Succ T) := 
  toFun : (a b : T) -> (L |- nat a) -> (L |- nat b) -> (L |- a * S b = a + (a * b))

abbrev mulNatSuccEqAddMul {L : Logic P}
  [N : IsNat P T] [Q : SEq P T] [M : SMul T] [A : SAdd T] [S : Succ T]
  [K : MulNatSuccEqAddMul L N Q M A S] {a b} := K.toFun a b

--------------------------------------------------------------------------------
-- Commmuted Axioms
--------------------------------------------------------------------------------

-- Axiom 1 Commuted
-- 0 * a = 0

class MulZeroNatEqZero (L : Logic P)
  (N : IsNat P T) (Q : SEq P T) (M : SMul T) (Z : Zero T)  :=
  toFun : (a : T) -> (L |- nat a) -> (L |- 0 * a = 0)

abbrev mulZeroNatEqZero {L : Logic P}
  [N : IsNat P T] [Q : SEq P T] [M : SMul T] [Z : Zero T] 
  [K : MulZeroNatEqZero L N Q M Z] {a} := K.toFun a

-- Axiom 2 Commuted
-- S a * b = b + (a * b)

class MulSuccNatEqAddMul (L : Logic P)
  (N : IsNat P T) (Q : SEq P T) (M : SMul T) (A : SAdd T) (S : Succ T) := 
  toFun : (a b : T) -> (L |- nat a) -> (L |- nat b) -> (L |- S a * b = b + (a * b))

abbrev mulSuccNatEqAddMul {L : Logic P}
  [N : IsNat P T] [Q : SEq P T] [M : SMul T] [A : SAdd T] [S : Succ T]
  [K : MulSuccNatEqAddMul L N Q M A S] {a b} := K.toFun a b

--------------------------------------------------------------------------------
-- Special Cases
--------------------------------------------------------------------------------

-- 0 * 0 = 0

class MulZeroEqZero (L : Logic P)
  (Q : SEq P T) (M : SMul T) (Z : Zero T) :=
  toFun : L |- 0 * 0 = (0 : T)

abbrev mulZeroEqZero {L : Logic P}
  [Q : SEq P T] [M : SMul T] [Z : Zero T] 
  [K : MulZeroEqZero L Q M Z] := K.toFun

-- a * 1 = a

class MulNatOneEqNat (L : Logic P)
  (N : IsNat P T) (Q : SEq P T) (M : SMul T) (O : One T) :=
  toFun : (a : T) -> (L |- nat a) -> (L |- a * 1 = a)

abbrev mulNatOneEqNat {L : Logic P}
  [N : IsNat P T] [Q : SEq P T] [M : SMul T] [O : One T]
  [K : MulNatOneEqNat L N Q M O] {a} := K.toFun a

-- 1 * a = a

class MulOneNatEqNat (L : Logic P)
  (N : IsNat P T) (Q : SEq P T) (M : SMul T) (O : One T) :=
  toFun : (a : T) -> (L |- nat a) -> (L |- 1 * a = a)

abbrev mulOneNatEqNat {L : Logic P}
  [N : IsNat P T] [Q : SEq P T] [M : SMul T] [O : One T]
  [K : MulOneNatEqNat L N Q M O] {a} := K.toFun a

--------------------------------------------------------------------------------
-- Commutativity
--------------------------------------------------------------------------------

-- 0 * a = a * 0

class MulNatZeroComm (L : Logic P)
  (N : IsNat P T) (Q : SEq P T) (M : SMul T) (Z : Zero T) :=
  toFun : (a : T) -> (L |- nat a) -> (L |- a * 0 = 0 * a)

abbrev mulNatZeroComm {L : Logic P}
  [N : IsNat P T] [Q : SEq P T] [M : SMul T] [Z : Zero T]
  [K : MulNatZeroComm L N Q M Z] {a} := K.toFun a

-- a * b = b * a

class MulNatComm (L : Logic P)
  (N : IsNat P T) (Q : SEq P T) (M : SMul T) :=
  toFun : (a b : T) -> (L |- nat a) -> (L |- nat b) -> (L |- a * b = b * a)

instance iCommOverTOfMulNatCommOverT 
  {L : Logic P}[N : IsNat P T] [Q : SEq P T] [M : SMul T] 
  [K : MulNatComm L N Q M] : CommOverT L Q.toFun N.isNat M.toFun 
  := {toFun := K.toFun}

instance iMulNatCommOverOfCommOverT 
  {L : Logic P} [N : IsNat P T] [Q : SEq P T] [M : SMul T] 
  [K : CommOverT L Q.toFun N.isNat M.toFun] : MulNatComm L N Q M
  := {toFun := K.toFun}

abbrev mulNatComm {L : Logic P}
  [N : IsNat P T] [Q : SEq P T] [M : SMul T]
  [K : MulNatComm L N Q M] {a b} := K.toFun a b

--------------------------------------------------------------------------------
-- Associativity
-- (a * b) * c = a * (b * c)
--------------------------------------------------------------------------------

class MulNatAssoc (L : Logic P)
  (N : IsNat P T) (Q : SEq P T) (M : SMul T) :=
  toFun :  (a b c : T) -> 
    (L |- nat a) -> (L |- nat b) -> (L |- nat c) ->
    (L |- (a * b) * c = a * (b * c))

instance iLtrAssocOverTOfMulNatAssoc 
  {L : Logic P} [N : IsNat P T] [Q : SEq P T] [M : SMul T] 
  [K : MulNatAssoc L N Q M] : LtrAssocOverT L Q.toFun N.isNat M.toFun 
  := {toFun := K.toFun}

instance iMulNatAssocOfLtrAssocOverT 
  {L : Logic P} [N : IsNat P T] [Q : SEq P T] [M : SMul T] 
  [K : LtrAssocOverT L Q.toFun N.isNat M.toFun] : MulNatAssoc L N Q M 
  := {toFun := K.toFun}

abbrev mulNatAssoc {L : Logic P}
  [N : IsNat P T] [Q : SEq P T] [M : SMul T]
  [K : MulNatAssoc L N Q M] {a b c} := K.toFun a b c

--------------------------------------------------------------------------------
-- Distributivity
--------------------------------------------------------------------------------

-- Left Distributive Over Addition
-- a * (b + c) = (a * b) + (a * c)

class MulNatAddEqAddMul (L : Logic P)
  (N : IsNat P T) (Q : SEq P T) (M : SMul T) (A : SAdd T) := 
  toFun : (a b c : T) -> 
    (L |- nat a) -> (L |- nat b) -> (L |- nat c) ->
    (L |- a * (b + c) = (a * b) + (a * c))

abbrev mulNatAddEqAddMul {L : Logic P}
  [N : IsNat P T] [Q : SEq P T] [M : SMul T] [A : SAdd T]
  [K : MulNatAddEqAddMul L N Q M A] {a b c} := K.toFun a b c

-- Right Distributive Over Addition
-- (b + c) * a = (b * a) + (c * a)

class MulAddNatEqAddMul (L : Logic P)
  (N : IsNat P T) (Q : SEq P T) (M : SMul T) (A : SAdd T) := 
  toFun : (a b c : T) -> 
    (L |- nat a) -> (L |- nat b) -> (L |- nat c) ->
    (L |- (b + c) * a = (b * a) + (c * a))

abbrev mulAddNatEqAddMul {L : Logic P}
  [N : IsNat P T] [Q : SEq P T] [M : SMul T] [A : SAdd T]
  [K : MulAddNatEqAddMul L N Q M A] {a b c} := K.toFun a b c

--------------------------------------------------------------------------------
-- Substitutivity
--------------------------------------------------------------------------------

-- (a = b) -> (c * a = c * b)

class EqNatMulNatLeft (L : Logic P)
  (N : IsNat P T) (Q : SEq P T) (M : SMul T) :=
  toFun : (a b c : T) -> 
    (L |- nat a) -> (L |- nat b) -> (L |- nat c) ->
    (L |- a = b) -> (L |- c * a = c * b)

instance iLeftReflTOfEqNatMulNatLeft {L : Logic P}
  [N : IsNat P T] [Q : SEq P T] [M : SMul T] 
  [K : EqNatMulNatLeft L N Q M] : LeftReflT L Q.toFun N.isNat M.toFun 
  := {toFun := fun a b c Na Nb Nc => K.toFun b c a Nb Nc Na}

instance iEqNatMulNatLeftTOfLeftReflT {L : Logic P}
  [N : IsNat P T] [Q : SEq P T] [M : SMul T] 
  [K : LeftReflT L Q.toFun N.isNat M.toFun] : EqNatMulNatLeft L N Q M
  := {toFun := fun a b c Na Nb Nc => K.toFun c a b Nc Na Nb}

abbrev eqNatMulNatLeft {L : Logic P}
  [N : IsNat P T] [Q : SEq P T] [M : SMul T]
  [K : EqNatMulNatLeft L N Q M] {a b c} := K.toFun a b c

abbrev eqNatMulNatLeft' {L : Logic P} 
  [N : IsNat P T] [Q : SEq P T] [M : SMul T] [K : EqNatMulNatLeft L N Q M] 
  {c a b} (Nc Na Nb) := K.toFun a b c Na Nb Nc

-- (a = b) -> (a * c = b * c)

class EqNatMulNatRight (L : Logic P)
  (N : IsNat P T) (Q : SEq P T) (M : SMul T) :=
  toFun : (a b c : T) -> 
    (L |- nat a) -> (L |- nat b) -> (L |- nat c) ->
    (L |- a = b) -> (L |- a * c = b * c)

instance iRightReflTOfEqNatMulNatRight 
  {L : Logic P} [N : IsNat P T] [Q : SEq P T] [M : SMul T] 
  [K : EqNatMulNatRight L N Q M] : RightReflT L Q.toFun N.isNat M.toFun 
  := {toFun := fun a b c Na Nb Nc => K.toFun b c a Nb Nc Na}

instance iEqNatMulNatRightOfRightReflT 
  {L : Logic P} [N : IsNat P T] [Q : SEq P T] [M : SMul T] 
  [K : RightReflT L Q.toFun N.isNat M.toFun] : EqNatMulNatRight L N Q M
  := {toFun := fun a b c Na Nb Nc => K.toFun c a b Nc Na Nb}

abbrev eqNatMulNatRight {L : Logic P}
  [N : IsNat P T] [Q : SEq P T] [M : SMul T]
  [K : EqNatMulNatRight L N Q M] {a b c} := K.toFun a b c

abbrev eqNatMulNatRight' {L : Logic P} 
  [N : IsNat P T] [Q : SEq P T] [M : SMul T] [K : EqNatMulNatRight L N Q M] 
  {c a b} (Nc Na Nb) := K.toFun a b c Na Nb Nc

--------------------------------------------------------------------------------
-- Closure
--------------------------------------------------------------------------------

-- nat (0 * 0)

class NatMulZero (L : Logic P) (N : IsNat P T) (M : SMul T) (Z : Zero T) :=
  toFun : L |- nat (0 * 0 : T)

abbrev natMulZero {L : Logic P} [N : IsNat P T] [M : SMul T] [Z : Zero T]
  [K : NatMulZero L N M Z] := K.toFun

-- nat (a * 0)

class NatMulNatZero (L : Logic P) (N : IsNat P T) (M : SMul T) (Z : Zero T) :=
  toFun : (a : T) -> (L |- nat a) -> (L |- nat (a * 0))

abbrev natMulNatZero {L : Logic P} [N : IsNat P T] [M : SMul T] [Z : Zero T]
  [K : NatMulNatZero L N M Z] {a} := K.toFun a

-- nat (0 * a)

class NatMulZeroNat (L : Logic P) (N : IsNat P T) (M : SMul T) (Z : Zero T) :=
  toFun : (a : T) -> (L |- nat a) -> (L |- nat (0 * a))

abbrev natMulZeroNat {L : Logic P} [N : IsNat P T] [M : SMul T] [Z : Zero T]
  [K : NatMulZeroNat L N M Z] {a} := K.toFun a 

-- nat (a * b)

class NatMulNat (L : Logic P) (N : IsNat P T) (M : SMul T) :=
  toFun : (a b : T) -> (L |- nat a) -> (L |- nat b) -> (L |- nat (a * b))

abbrev natMulNat {L : Logic P}[N : IsNat P T] [M : SMul T] 
  [K : NatMulNat L N M] {a b} := K.toFun a b

abbrev natMul {L : Logic P} [N : IsNat P T] [M : SMul T] 
  [K : NatMulNat L N M]{a b} := K.toFun a b
