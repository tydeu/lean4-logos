import Gaea.Math.Syntax
import Gaea.Logic.Judgment
import Gaea.Peano.Nat

universes u v w
variable {P : Sort u} {T : Sort v} 

open Gaea.Notation
namespace Gaea.Peano

--------------------------------------------------------------------------------
-- Meta (Structural) Induction
--------------------------------------------------------------------------------

-- Axiom N9 (Alt)
class MetaNatInduction (L : Logic P) (N : PNat P T) := 
  toFun : (f : T -> Sort w) -> f 0 ->
    ((n : T) -> (L |- nat n) -> (f n -> f (S n))) ->
    ((n : T) -> (L |- nat n) -> f n)

def metaNatInduction (L : Logic P) [N : PNat P T] 
  [K : MetaNatInduction L N] {f} := K.toFun f

--------------------------------------------------------------------------------
-- Predicate Induction
--------------------------------------------------------------------------------

-- Axiom N9
class NatInduction (L : Logic P) (N : PNat P T) := 
  toFun : (f : Pred P T) -> (L |- f 0) -> 
    ((n : T) -> (L |- nat n) -> (L |- f n) -> (L |- f (S n))) ->
    ((n : T) -> (L |- nat n) -> (L |- f n))

def natInduction {L : Logic P} [N : PNat P T] 
  [K : NatInduction L N] {F} := K.toFun F

--------------------------------------------------------------------------------
-- Relation Induction
--------------------------------------------------------------------------------

-- Left Induction

class NatInductionLeft (L : Logic P) (N : PNat P T) := 
  toFun : (R : Rel P T) -> 
    ((b : T) -> (L |- nat b) -> (L |- R 0 b)) -> 
    ((a : T) -> (L |- nat a) ->
      ((b : T) -> (L |- nat b) -> (L |- R a b)) -> 
      ((b : T) -> (L |- nat b) -> (L |- R (S a) b))) ->
    ((a b : T) -> (L |- nat a) -> (L |- nat b) -> (L |- R a b))

def natInductionLeft {L : Logic P} [N : PNat P T] 
  [K : NatInductionLeft L N] {R} := K.toFun R

-- Right Induction

class NatInductionRight (L : Logic P) (N : PNat P T) := 
  toFun : (R : Rel P T) -> 
    ((a : T) -> (L |- nat a) -> (L |- R a 0)) -> 
    ((b : T) -> (L |- nat b) -> 
      ((a : T) -> (L |- nat a) -> (L |- R a b)) -> 
      ((a : T) -> (L |- nat a) -> (L |- R a (S b)))) ->
    ((a b : T) -> (L |- nat a) -> (L |- nat b) -> (L |- R a b))

def natInductionRight {L : Logic P} [N : PNat P T] 
  [K : NatInductionRight L N] {R} := K.toFun R

--------------------------------------------------------------------------------
-- Ternary Induction
--------------------------------------------------------------------------------

-- Left Induction

class NatInductionLeft3 (L : Logic P) (N : PNat P T) := 
  (toFun : (R : T -> T -> T -> P) -> 
    ((b c : T) -> (L |- nat b) -> (L |- nat c) ->  
      (L |- R 0 b c)) -> 
    ((a : T) -> (L |- nat a) ->
      ((b c : T) -> (L |- nat b) -> (L |- nat c) -> (L |- R a b c)) -> 
      ((b c : T) -> (L |- nat b) -> (L |- nat c) -> (L |- R (S a) b c))) ->
    ((a b c : T) -> (L |- nat a) -> (L |- nat b) -> (L |- nat c) -> 
      (L |- R a b c)))

def natInductionLeft3 {L : Logic P} [N : PNat P T] 
  [K : NatInductionLeft3 L N] {R} := K.toFun R

-- Middle Induction

class NatInductionMiddle (L : Logic P) (N : PNat P T) := 
  (toFun : (R : T -> T -> T -> P) -> 
    ((a c : T) -> (L |- nat a) -> (L |- nat c) ->  
      (L |- R a 0 c)) -> 
    ((b : T) -> (L |- nat b) ->
      ((a c : T) -> (L |- nat a) -> (L |- nat c) -> (L |- R a b c)) -> 
      ((a c : T) -> (L |- nat a) -> (L |- nat c) -> (L |- R (S a) b c))) ->
    ((a b c : T) -> (L |- nat a) -> (L |- nat b) -> (L |- nat c) -> 
      (L |- R a b c)))

def natInductionMiddle {L : Logic P} [N : PNat P T] 
  [K : NatInductionMiddle L N] {R} := K.toFun R

-- Right Induction

class NatInductionRight3 (L : Logic P) (N : PNat P T) := 
  toFun : (R : T -> T -> T -> P) -> 
    ((a b : T) -> (L |- nat a) -> (L |- nat b) ->  
      (L |- R a b 0)) -> 
    ((c : T) -> (L |- nat c) ->
      ((a b : T) -> (L |- nat a) -> (L |- nat b) -> (L |- R a b c)) -> 
      ((a b : T) -> (L |- nat a) -> (L |- nat b) -> (L |- R a b (S c)))) ->
    ((a b c : T) -> (L |- nat a) -> (L |- nat b) -> (L |- nat c) -> 
      (L |- R a b c))

def natInductionRight3 {L : Logic P} [N : PNat P T] 
  [K : NatInductionRight3 L N] {R} := K.toFun R

-- Right Conditional Induction

class NatInductionRight3If (L : Logic P) (N : PNat P T) := 
  toFun : (C : Rel P T) -> (R : T -> T -> T -> P) ->
    ((a b : T) -> (L |- nat a) -> (L |- nat b) ->  
      (L |- C a b) -> (L |- R a b 0)) -> 
    ((c : T) -> (L |- nat c) -> 
      ((a b : T) -> (L |- nat a) -> (L |- nat b) -> 
        (L |- C a b) -> (L |- R a b c)) ->
      ((a b : T) -> (L |- nat a) -> (L |- nat b) -> 
        (L |- C a b) -> (L |- R a b (S c)))) ->
    ((a b c : T) -> (L |- nat a) -> (L |- nat b) -> (L |- nat c) -> 
      (L |- C a b) -> (L |- R a b c))

def natInductionRight3If {L : Logic P} [N : PNat P T] 
  [K : NatInductionRight3If L N] {C R} := K.toFun C R 
