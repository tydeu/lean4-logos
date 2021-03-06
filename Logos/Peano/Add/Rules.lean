import Logos.Peano.Eq
import Logos.Peano.Nat
import Logos.Math.Syntax

universes u v
variable {P : Sort u} {T : Sort v} 

open Logos.Notation
namespace Logos.Peano

--------------------------------------------------------------------------------
-- Axioms
--------------------------------------------------------------------------------

-- Axiom 1
class AddNatZeroEqNat (L : Logic P) 
  (N : SNat P T) (Q : SEq P T) (A : SAdd T) (Z : Zero T) :=
  toFun : (a : T) -> (L |- nat a) -> (L |- a + 0 = a)

abbrev addNatZeroEqNat {L : Logic P} 
  [N : SNat P T] [Q : SEq P T] [A : SAdd T] [Z : Zero T] 
  [K : AddNatZeroEqNat L N Q A Z] {a} := K.toFun a

-- Axiom 2
class AddNatSuccEqSucc (L : Logic P) 
  (N : SNat P T) (Q : SEq P T) (A : SAdd T) (S : Succ T) := 
  toFun : (a b : T) -> (L |- nat a) -> (L |- nat b) -> 
    (L |- a + S b = S (a + b))

abbrev addNatSuccEqSucc {L : Logic P} 
  [N : SNat P T] [Q : SEq P T] [A : SAdd T] [S : Succ T]
  [K : AddNatSuccEqSucc L N Q A S] {a b} := K.toFun a b

--------------------------------------------------------------------------------
-- Commuted Axioms
--------------------------------------------------------------------------------

-- Axiom 1 Commuted
class AddZeroNatEqNat (L : Logic P) 
  (N : SNat P T) (Q : SEq P T) (A : SAdd T) (Z : Zero T) :=
  toFun : (a : T) -> (L |- nat a) -> (L |- 0 + a = a)

abbrev addZeroNatEqNat {L : Logic P} 
  [N : SNat P T] [Q : SEq P T] [A : SAdd T] [Z : Zero T] 
  [K : AddZeroNatEqNat L N Q A Z] {a} := K.toFun a

-- Axiom 2 Commuted
class AddSuccNatEqSucc (L : Logic P) 
  (N : SNat P T) (Q : SEq P T) (A : SAdd T) (S : Succ T) := 
  toFun : (a b : T) -> (L |- nat a) -> (L |- nat b) -> 
    (L |- S a + b = S (a + b))

abbrev addSuccNatEqSucc {L : Logic P} 
  [N : SNat P T] [Q : SEq P T] [A : SAdd T] [S : Succ T]
  [K : AddSuccNatEqSucc L N Q A S] {a b} := K.toFun a b

--------------------------------------------------------------------------------
-- Special Cases
--------------------------------------------------------------------------------

-- 0 + 0 = 0

class AddZeroEqZero (L : Logic P) 
  (Q : SEq P T) (A : SAdd T) (Z : Zero T) :=
  toFun : L |- 0 + 0 = (0 : T)

abbrev addZeroEqZero {L : Logic P} 
  [Q : SEq P T] [A : SAdd T] [Z : Zero T] 
  [K : AddZeroEqZero L Q A Z] := K.toFun

-- a + 1 = S a

class AddNatOneEqSucc (L : Logic P) 
  (N : SNat P T) (Q : SEq P T) (A : SAdd T) (O : One T) (S : Succ T) :=
  toFun : (a : T) -> (L |- nat a) -> (L |- a + 1 = S a)

abbrev addNatOneEqSucc {L : Logic P} 
  [N : SNat P T] [Q : SEq P T] [A : SAdd T] [O : One T] [S : Succ T]
  [K : AddNatOneEqSucc L N Q A O S] {a} := K.toFun a

-- 1 + a = S a

class AddOneNatEqSucc (L : Logic P) 
  (N : SNat P T) (Q : SEq P T) (A : SAdd T) (O : One T) (S : Succ T) :=
  toFun : (a : T) -> (L |- nat a) -> (L |- 1 + a = S a)

abbrev addOneNatEqSucc {L : Logic P} 
  [N : SNat P T] [Q : SEq P T] [A : SAdd T] [O : One T] [S : Succ T]
  [K : AddOneNatEqSucc L N Q A O S] {a} := K.toFun a

--------------------------------------------------------------------------------
-- Commutativity
--------------------------------------------------------------------------------

-- 0 + a = a + 0

class AddNatZeroComm (L : Logic P) 
  (N : SNat P T) (Q : SEq P T) (A : SAdd T) (Z : Zero T) :=
  toFun : (a : T) -> (L |- nat a) -> (L |- a + 0 = 0 + a)

abbrev addNatZeroComm {L : Logic P} 
  [N : SNat P T] [Q : SEq P T] [A : SAdd T] [Z : Zero T]
  [K : AddNatZeroComm L N Q A Z] {a} := K.toFun a

-- a + b = b + a

class AddNatComm (L : Logic P) 
  (N : SNat P T) (Q : SEq P T) (A : SAdd T) :=
  toFun : (a b : T) -> (L |- nat a) -> (L |- nat b) -> (L |- a + b = b + a)

instance iCommOverTOfAddNatComm 
  {L : Logic P} [N : SNat P T] [Q : SEq P T] [A : SAdd T] 
  [K : AddNatComm L N Q A] : CommOverT L Q.toFun N.mem A.toFun 
  := {toFun := K.toFun}

instance iAddNatCommOverTOfComm 
  {L : Logic P} [N : SNat P T] [Q : SEq P T] [A : SAdd T] 
  [K : CommOverT L Q.toFun N.mem A.toFun ] : AddNatComm L N Q A
  := {toFun := K.toFun}

abbrev addNatComm {L : Logic P} 
  [N : SNat P T] [Q : SEq P T] [A : SAdd T]
  [K : AddNatComm L N Q A] {a b} := K.toFun a b

--------------------------------------------------------------------------------
-- Associativity
--------------------------------------------------------------------------------

-- (a + b) + c = a + (b + c)

class AddNatAssoc (L : Logic P) 
  (N : SNat P T) (Q : SEq P T) (A : SAdd T) :=
  toFun :  (a b c : T) -> 
    (L |- nat a) -> (L |- nat b) -> (L |- nat c) ->
    (L |- (a + b) + c = a + (b + c))

instance iLtrAssocOverTOfAddNatAssoc 
  {L : Logic P} [N : SNat P T] [Q : SEq P T] [A : SAdd T] 
  [K : AddNatAssoc L N Q A] : LtrAssocOverT L Q.toFun N.mem A.toFun 
  := {toFun := K.toFun}

instance iAddNatAssocOfLtrAssocOverT 
  {L : Logic P} [N : SNat P T] [Q : SEq P T] [A : SAdd T] 
  [K : LtrAssocOverT L Q.toFun N.mem A.toFun] : AddNatAssoc L N Q A 
  := {toFun := K.toFun}

abbrev addNatAssoc {L : Logic P} [N : SNat P T] [Q : SEq P T] [A : SAdd T]
  [K : AddNatAssoc L N Q A] {a b c} := K.toFun a b c

-- a + (b + c) = (a + b) + c 

class AddNatAssocRev (L : Logic P) 
  (N : SNat P T) (Q : SEq P T) (A : SAdd T) :=
  toFun :  (a b c : T) -> 
    (L |- nat a) -> (L |- nat b) -> (L |- nat c) ->
    (L |- a + (b + c) = (a + b) + c)

abbrev addNatAssocRev {P : Sort u} {T : Sort v}
  {L : Logic P} [N : SNat P T] [Q : SEq P T] [A : SAdd T]
  [K : AddNatAssocRev L N Q A] {a b c} := K.toFun a b c

--------------------------------------------------------------------------------
-- Substitutivity
--------------------------------------------------------------------------------

-- (a = b) -> (c + a = c + b)

class EqNatAddNatLeft (L : Logic P) 
  (N : SNat P T) (Q : SEq P T) (A : SAdd T) :=
  toFun : (a b c : T) -> 
    (L |- nat a) -> (L |- nat b) -> (L |- nat c) ->
    (L |- a = b) -> (L |- c + a = c + b)

instance iLeftApplyTOfEqNatAddNatLeft 
  {L : Logic P} [N : SNat P T] [Q : SEq P T] [A : SAdd T] 
  [K : EqNatAddNatLeft L N Q A] : LeftApplyT L Q.toFun N.mem A.toFun 
  := {toFun := fun a b c Na Nb Nc => K.toFun b c a Nb Nc Na}

instance iEqNatAddNatLeftTOfLeftApplyT 
  {L : Logic P} [N : SNat P T] [Q : SEq P T] [A : SAdd T] 
  [K : LeftApplyT L Q.toFun N.mem A.toFun] : EqNatAddNatLeft L N Q A
  := {toFun := fun a b c Na Nb Nc => K.toFun c a b Nc Na Nb}

abbrev eqNatAddNatLeft {L : Logic P} 
  [N : SNat P T] [Q : SEq P T] [A : SAdd T]
  [K : EqNatAddNatLeft L N Q A] {a b c} := K.toFun a b c

abbrev eqNatAddNatLeft' {L : Logic P} 
  [N : SNat P T] [Q : SEq P T] [A : SAdd T] [K : EqNatAddNatLeft L N Q A] 
  {c a b} (Nc Na Nb) := K.toFun a b c Na Nb Nc

-- (a = b) -> (a + c = b + c)

class EqNatAddNatRight (L : Logic P) 
  (N : SNat P T) (Q : SEq P T) (A : SAdd T) :=
  toFun : (a b c : T) -> 
    (L |- nat a) -> (L |- nat b) -> (L |- nat c) ->
    (L |- a = b) -> (L |- a + c = b + c)

instance iRightApplyTOfEqNatAddNatRight {L : Logic P} 
  [N : SNat P T] [Q : SEq P T] [A : SAdd T] 
  [K : EqNatAddNatRight L N Q A] : RightApplyT L Q.toFun N.mem A.toFun 
  := {toFun := fun a b c Na Nb Nc => K.toFun b c a Nb Nc Na}

instance iEqNatAddNatRightOfRightApplyT {L : Logic P} 
  [N : SNat P T] [Q : SEq P T] [A : SAdd T] 
  [K : RightApplyT L Q.toFun N.mem A.toFun] : EqNatAddNatRight L N Q A
  := {toFun := fun a b c Na Nb Nc => K.toFun c a b Nc Na Nb}

abbrev eqNatAddNatRight {L : Logic P}
  [N : SNat P T] [Q : SEq P T] [A : SAdd T]
  [K : EqNatAddNatRight L N Q A] {a b c} := K.toFun a b c

abbrev eqNatAddNatRight' {L : Logic P} 
  [N : SNat P T] [Q : SEq P T] [A : SAdd T] [K : EqNatAddNatRight L N Q A] 
  {c a b} (Nc Na Nb) := K.toFun a b c Na Nb Nc

--------------------------------------------------------------------------------
-- Closure
--------------------------------------------------------------------------------

-- nat (0 + 0)

class NatAddZero (L : Logic P) (N : SNat P T) (A : SAdd T) (Z : Zero T) :=
  toFun : L |- nat (0 + 0 : T)

abbrev natAddZero {L : Logic P} [N : SNat P T] [A : SAdd T] [Z : Zero T]
  [K : NatAddZero L N A Z] := K.toFun

-- nat (a + 0)

class NatAddNatZero (L : Logic P) (N : SNat P T) (A : SAdd T) (Z : Zero T) :=
  toFun : (a : T) -> (L |- nat a) -> (L |- nat (a + 0))

abbrev natAddNatZero {L : Logic P} [N : SNat P T] [A : SAdd T] [Z : Zero T]
  [K : NatAddNatZero L N A Z] {a} := K.toFun a

-- nat (0 + a)

class NatAddZeroNat (L : Logic P) (N : SNat P T) (A : SAdd T) (Z : Zero T) :=
  toFun : (a : T) -> (L |- nat a) -> (L |- nat (0 + a))

abbrev natAddZeroNat {L : Logic P} [N : SNat P T] [A : SAdd T] [Z : Zero T]
  [K : NatAddZeroNat L N A Z] {a} := K.toFun a 

-- nat (a + b)

class NatAddNat (L : Logic P) (N : SNat P T) (A : SAdd T) :=
  toFun : (a b : T) -> (L |- nat a) -> (L |- nat b) -> (L |- nat (a + b))

abbrev natAddNat {L : Logic P} [N : SNat P T] [A : SAdd T] 
  [K : NatAddNat L N A] {a b} := K.toFun a b

abbrev natAdd {L : Logic P} [N : SNat P T] [A : SAdd T] 
  [K : NatAddNat L N A] {a b} := K.toFun a b
