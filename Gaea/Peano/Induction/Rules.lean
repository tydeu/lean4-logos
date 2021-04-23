import Gaea.Math.Notation
import Gaea.Logic.Judgment
import Gaea.Peano.Nat

universes u v w
variable {P : Sort u} {T : Sort v} 

open Gaea.Math
open Gaea.Logic

namespace Gaea.Peano

--------------------------------------------------------------------------------
-- Predicate Induction
--------------------------------------------------------------------------------

-- Axiom N9
class NatInduction (L : Logic P) (N : PNat P T) := 
  toFun : (f : T -> P) -> (L |- f 0) -> 
    ((n : T) -> (L |- nat n) -> (L |- f n) -> (L |- f (S n))) ->
    ((n : T) -> (L |- nat n) -> (L |- f n))

def natInduction {L : Logic P} [N : PNat P T] 
  [K : NatInduction L N] {f} := K.toFun f

--------------------------------------------------------------------------------
-- Schema Induction
--------------------------------------------------------------------------------

-- Axiom N9 (Alt)
class NatInduction' (L : Logic P) (N : PNat P T) := 
  toFun : (f : T -> Sort w) -> f 0 ->
    ((n : T) -> (L |- nat n) -> (f n -> f (S n))) ->
    ((n : T) -> (L |- nat n) -> f n)

def natInduction' (L : Logic P) [N : PNat P T] 
  [K : NatInduction' L N] {f} := K.toFun f

--------------------------------------------------------------------------------
-- Relation Induction
--------------------------------------------------------------------------------

-- Left Induction

class NatInductionLeft (L : Logic P) (N : PNat P T) := 
  toFun : (f : T -> T -> P) -> 
    ((b : T) -> (L |- nat b) -> (L |- f 0 b)) -> 
    ((a : T) -> (L |- nat a) ->
      ((b : T) -> (L |- nat b) -> (L |- f a b)) -> 
      ((b : T) -> (L |- nat b) -> (L |- f (S a) b))) ->
    ((a b : T) -> (L |- nat a) -> (L |- nat b) -> (L |- f a b))

def natInductionLeft {L : Logic P} [N : PNat P T] 
  [K : NatInductionLeft L N] {f} := K.toFun f

-- Right Induction

class NatInductionRight (L : Logic P) (N : PNat P T) := 
  toFun : (f : T -> T -> P) -> 
    ((a : T) -> (L |- nat a) -> (L |- f a 0)) -> 
    ((b : T) -> (L |- nat b) -> 
      ((a : T) -> (L |- nat a) -> (L |- f a b)) -> 
      ((a : T) -> (L |- nat a) -> (L |- f a (S b)))) ->
    ((a b : T) -> (L |- nat a) -> (L |- nat b) -> (L |- f a b))

def natInductionRight {L : Logic P} [N : PNat P T] 
  [K : NatInductionRight L N] {f} := K.toFun f

--------------------------------------------------------------------------------
-- Ternary Induction
--------------------------------------------------------------------------------

-- Left Induction

class NatInductionLeft3 (L : Logic P) (N : PNat P T) := 
  (toFun : (f : T -> T -> T -> P) -> 
    ((b c : T) -> (L |- nat b) -> (L |- nat c) ->  
      (L |- f 0 b c)) -> 
    ((a : T) -> (L |- nat a) ->
      ((b c : T) -> (L |- nat b) -> (L |- nat c) -> (L |- f a b c)) -> 
      ((b c : T) -> (L |- nat b) -> (L |- nat c) -> (L |- f (S a) b c))) ->
    ((a b c : T) -> (L |- nat a) -> (L |- nat b) -> (L |- nat c) -> 
      (L |- f a b c)))

def natInductionLeft3 {L : Logic P} [N : PNat P T] 
  [K : NatInductionLeft3 L N] {f} := K.toFun f

-- Middle Induction

class NatInductionMiddle (L : Logic P) (N : PNat P T) := 
  (toFun : (f : T -> T -> T -> P) -> 
    ((a c : T) -> (L |- nat a) -> (L |- nat c) ->  
      (L |- f a 0 c)) -> 
    ((b : T) -> (L |- nat b) ->
      ((a c : T) -> (L |- nat a) -> (L |- nat c) -> (L |- f a b c)) -> 
      ((a c : T) -> (L |- nat a) -> (L |- nat c) -> (L |- f (S a) b c))) ->
    ((a b c : T) -> (L |- nat a) -> (L |- nat b) -> (L |- nat c) -> 
      (L |- f a b c)))

def natInductionMiddle {L : Logic P} [N : PNat P T] 
  [K : NatInductionMiddle L N] {f} := K.toFun f

-- Right Induction

class NatInductionRight3 (L : Logic P) (N : PNat P T) := 
  toFun : (f : T -> T -> T -> P) -> 
    ((a b : T) -> (L |- nat a) -> (L |- nat b) ->  
      (L |- f a b 0)) -> 
    ((c : T) -> (L |- nat c) ->
      ((a b : T) -> (L |- nat a) -> (L |- nat b) -> (L |- f a b c)) -> 
      ((a b : T) -> (L |- nat a) -> (L |- nat b) -> (L |- f a b (S c)))) ->
    ((a b c : T) -> (L |- nat a) -> (L |- nat b) -> (L |- nat c) -> 
      (L |- f a b c))

def natInductionRight3 {L : Logic P} [N : PNat P T] 
  [K : NatInductionRight3 L N] {f} := K.toFun f

class NatInductionRight3If (L : Logic P) (N : PNat P T) := 
  toFun : (C : T -> T -> P) -> (f : T -> T -> T -> P) ->
    ((a b : T) -> (L |- nat a) -> (L |- nat b) ->  
      (L |- C a b) -> (L |- f a b 0)) -> 
    ((c : T) -> (L |- nat c) -> 
      ((a b : T) -> (L |- nat a) -> (L |- nat b) -> 
        (L |- C a b) -> (L |- f a b c)) ->
      ((a b : T) -> (L |- nat a) -> (L |- nat b) -> 
        (L |- C a b) -> (L |- f a b (S c)))) ->
    ((a b c : T) -> (L |- nat a) -> (L |- nat b) -> (L |- nat c) -> 
      (L |- C a b) -> (L |- f a b c))

def natInductionRight3If {L : Logic P} [N : PNat P T] 
  [K : NatInductionRight3If L N] {C f} := K.toFun C f 

end Gaea.Peano
