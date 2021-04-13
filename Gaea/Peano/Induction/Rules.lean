import Gaea.Math.Notation
import Gaea.Logic.Judgment
import Gaea.Peano.Nat

universes u v w

open Gaea.Math
open Gaea.Logic

namespace Gaea.Peano

--------------------------------------------------------------------------------
-- Predicate Induction
--------------------------------------------------------------------------------

-- Axiom N9
class NatInduction {P : Sort u} {T : Type v} 
  (L : Logic P) (N : PNat P T) := 
  (natInduction : 
    (f : T -> P) -> (L |- f 0) -> 
    ((n : T) -> (L |- nat n) -> (L |- f n) -> (L |- f (S n))) ->
    ((n : T) -> (L |- nat n) -> (L |- f n)))

def natInduction {P : Sort u} {T : Type v} {L : Logic P} [N : PNat P T] 
  [K : NatInduction L N] {f} := K.natInduction f

--------------------------------------------------------------------------------
-- Schema Induction
--------------------------------------------------------------------------------

-- Axiom N9 (Alt)
class NatInduction' {P : Sort u} {T : Type v} 
  (L : Logic P) (N : PNat P T) := 
  (natInduction' : 
    (f : T -> Sort w) -> f 0 ->
    ((n : T) -> (L |- nat n) -> (f n -> f (S n))) ->
    ((n : T) -> (L |- nat n) -> f n))

def natInduction' {P : Sort u} {T : Type v} (L : Logic P) [N : PNat P T] 
  [K : NatInduction' L N] {f} := K.natInduction' f

--------------------------------------------------------------------------------
-- Relation Induction
--------------------------------------------------------------------------------

-- Left Induction

class NatInductionLeft {P : Sort u} {T : Type v} 
  (L : Logic P) (N : PNat P T) := 
  (natInductionLeft : 
    (f : T -> T -> P) -> 
    ((b : T) -> (L |- nat b) -> (L |- f 0 b)) -> 
    ((a : T) -> (L |- nat a) ->
      ((b : T) -> (L |- nat b) -> (L |- f a b)) -> 
      ((b : T) -> (L |- nat b) -> (L |- f (S a) b))) ->
    ((a b : T) -> (L |- nat a) -> (L |- nat b) -> (L |- f a b)))

def natInductionLeft {P : Sort u} {T : Type v} {L : Logic P} [N : PNat P T] 
  [K : NatInductionLeft L N] {f} := K.natInductionLeft f

-- Right Induction

class NatInductionRight {P : Sort u} {T : Type v} 
  (L : Logic P) (N : PNat P T) := 
  (natInductionRight : 
    (f : T -> T -> P) -> 
    ((a : T) -> (L |- nat a) -> (L |- f a 0)) -> 
    ((b : T) -> (L |- nat b) -> 
      ((a : T) -> (L |- nat a) -> (L |- f a b)) -> 
      ((a : T) -> (L |- nat a) -> (L |- f a (S b)))) ->
    ((a b : T) -> (L |- nat a) -> (L |- nat b) -> (L |- f a b)))

def natInductionRight {P : Sort u} {T : Type v} {L : Logic P} [N : PNat P T] 
  [K : NatInductionRight L N] {f} := K.natInductionRight f

--------------------------------------------------------------------------------
-- Ternary Induction
--------------------------------------------------------------------------------

-- Left Induction

class NatInductionLeft3 {P : Sort u} {T : Type v} 
  (L : Logic P) (N : PNat P T) := 
  (natInductionLeft3 : 
    (f : T -> T -> T -> P) -> 
    ((b c : T) -> (L |- nat b) -> (L |- nat c) ->  
      (L |- f 0 b c)) -> 
    ((a : T) -> (L |- nat a) ->
      ((b c : T) -> (L |- nat b) -> (L |- nat c) -> (L |- f a b c)) -> 
      ((b c : T) -> (L |- nat b) -> (L |- nat c) -> (L |- f (S a) b c))) ->
    ((a b c : T) -> (L |- nat a) -> (L |- nat b) -> (L |- nat c) -> 
      (L |- f a b c)))

def natInductionLeft3 {P : Sort u} {T : Type v} {L : Logic P} [N : PNat P T] 
  [K : NatInductionLeft3 L N] {f} := K.natInductionLeft3 f

-- Middle Induction

class NatInductionMiddle {P : Sort u} {T : Type v} 
  (L : Logic P) (N : PNat P T) := 
  (natInductionMiddle : 
    (f : T -> T -> T -> P) -> 
    ((a c : T) -> (L |- nat a) -> (L |- nat c) ->  
      (L |- f a 0 c)) -> 
    ((b : T) -> (L |- nat b) ->
      ((a c : T) -> (L |- nat a) -> (L |- nat c) -> (L |- f a b c)) -> 
      ((a c : T) -> (L |- nat a) -> (L |- nat c) -> (L |- f (S a) b c))) ->
    ((a b c : T) -> (L |- nat a) -> (L |- nat b) -> (L |- nat c) -> 
      (L |- f a b c)))

def natInductionMiddle {P : Sort u} {T : Type v} {L : Logic P} [N : PNat P T] 
  [K : NatInductionMiddle L N] {f} := K.natInductionMiddle f

-- Right Induction

class NatInductionRight3 {P : Sort u} {T : Type v} 
  (L : Logic P) (N : PNat P T) := 
  (natInductionRight3 : 
    (f : T -> T -> T -> P) -> 
    ((a b : T) -> (L |- nat a) -> (L |- nat b) ->  
      (L |- f a b 0)) -> 
    ((c : T) -> (L |- nat c) ->
      ((a b : T) -> (L |- nat a) -> (L |- nat b) -> (L |- f a b c)) -> 
      ((a b : T) -> (L |- nat a) -> (L |- nat b) -> (L |- f a b (S c)))) ->
    ((a b c : T) -> (L |- nat a) -> (L |- nat b) -> (L |- nat c) -> 
      (L |- f a b c)))

def natInductionRight3 {P : Sort u} {T : Type v} {L : Logic P} [N : PNat P T] 
  [K : NatInductionRight3 L N] {f} := K.natInductionRight3 f

class NatInductionRight3If {P : Sort u} {T : Type v} 
  (L : Logic P) (N : PNat P T) := 
  (natInductionRight3If : 
    (C : T -> T -> P) -> (f : T -> T -> T -> P) ->
    ((a b : T) -> (L |- nat a) -> (L |- nat b) ->  
      (L |- C a b) -> (L |- f a b 0)) -> 
    ((c : T) -> (L |- nat c) -> 
      ((a b : T) -> (L |- nat a) -> (L |- nat b) -> 
        (L |- C a b) -> (L |- f a b c)) ->
      ((a b : T) -> (L |- nat a) -> (L |- nat b) -> 
        (L |- C a b) -> (L |- f a b (S c)))) ->
    ((a b c : T) -> (L |- nat a) -> (L |- nat b) -> (L |- nat c) -> 
      (L |- C a b) -> (L |- f a b c)))

def natInductionRight3If {P : Sort u} {T : Type v} {L : Logic P} [N : PNat P T] 
  [K : NatInductionRight3If L N] {C f} := K.natInductionRight3If C f 

end Gaea.Peano
