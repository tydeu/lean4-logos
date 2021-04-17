import Gaea.Logic.Judgment
import Gaea.Logic.Rel.Type

universes u v
variable {P : Sort u} {T : Sort v}

namespace Gaea.Logic

--------------------------------------------------------------------------------
-- Reflexivity
-- a -> (|- R a a)
--------------------------------------------------------------------------------

-- Unconstrained

class Refl (L : Logic P) (R : Rel P T) :=
  refl : (a : T) -> (L |- R a a)

def refl {L : Logic P} {R : Rel P T}
  [K : Refl L R] := K.refl

def rfl {L : Logic P} {R : Rel P T}
  [K : Refl L R] {a} := K.refl a

-- Constrained

class ReflT (L : Logic P) (R : Rel P T) (C : T -> P) :=
  reflT : (a : T) -> (L |- C a) -> (L |- R a a)

instance iReflOfReflT {L : Logic P} {R : Rel P T} {C}
  [K : Refl L R] : ReflT L R C := {reflT := fun a _ => K.refl a}

def reflT 
  {L : Logic P} {R : Rel P T} {C} 
  [K : ReflT L R C] {a} := K.reflT a

--------------------------------------------------------------------------------
-- Symmetry
-- R a b |- R b a
--------------------------------------------------------------------------------

-- Unconstrained

class Symm (L : Logic P) (R : Rel P T) :=
  symm : (a b : T) -> (L |- R a b) -> (L |- R b a)

def symm {L : Logic P} {R : Rel P T}
  [K : Symm L R] {a b} := K.symm a b

-- Constrained

class SymmT (L : Logic P) (R : Rel P T) (C : T -> P)  :=
  symmT : (a b : T) -> (L |- C a) -> (L |- C b) ->
    (L |- R a b) -> (L |- R b a)

instance iSymmOfSymmT {L : Logic P} {R : Rel P T} {C}
  [K : Symm L R] : SymmT L R C := {symmT := fun a b _ _ => K.symm a b}

def symmT {L : Logic P} {R : Rel P T} {C} 
  [K : SymmT L R C] {a b} := K.symmT a b 

--------------------------------------------------------------------------------
-- Transitivity
-- R a b, R b c |- R a c
--------------------------------------------------------------------------------

-- Unconstrained

class Trans (L : Logic P) (R : Rel P T) :=
  trans : (a b c : T) -> (L |- R a b) -> (L |- R b c) -> (L |- R a c)

def trans {L : Logic P} {R : Rel P T}
  [K : Trans L R] {a b c} := K.trans a b c 

def trans' {L : Logic P} {R : Rel P T}
  [K : Trans L R] (b) {a c} := K.trans a b c 

-- Constrained

class TransT (L : Logic P) (R : Rel P T) (C : T -> P) :=
  transT : (a b c : T) -> 
    (L |- C a) -> (L |- C b) -> (L |- C c) -> 
    (L |- R a b) -> (L |- R b c) -> (L |- R a c)

instance iTransOfTransT {L : Logic P} {R : Rel P T} {C}
  [K : Trans L R] : TransT L R C 
  := {transT := fun a b c _ _ _ => K.trans a b c}

def transT {L : Logic P} {R : Rel P T} {C} 
  [K : TransT L R C] {a b c : T} := K.transT a b c 

def transT' {L : Logic P} {R : Rel P T} {C} 
  [K : TransT L R C] {b a c Cb Ca Cc} := K.transT a b c Ca Cb Cc

--------------------------------------------------------------------------------
-- Left Euclidean
-- R b a, R c a |- R b c
--------------------------------------------------------------------------------

-- Unconstrained

class LeftEuc (L : Logic P) (R : Rel P T) :=
  leftEuc : (a b c : T) -> (L |- R b a) -> (L |- R c a) -> (L |- R b c)

def leftEuc {L : Logic P} {R : Rel P T}
  [K : LeftEuc L R] {a b c} := K.leftEuc a b c 

-- Constrained

class LeftEucT (L : Logic P) (R : Rel P T) (C : T -> P) :=
  leftEucT : (a b c : T) -> 
    (L |- C a) -> (L |- C b) -> (L |- C c) -> 
    (L |- R b a) -> (L |- R c a) -> (L |- R b c)

instance iLeftEucOfLeftEucT {L : Logic P} {R : Rel P T} {C}
  [K : LeftEuc L R] : LeftEucT L R C 
  := {leftEucT := fun a b c _ _ _ => K.leftEuc a b c}

def leftEucT {L : Logic P} {R : Rel P T} {C} 
  [K : LeftEucT L R C] {a b c} := K.leftEucT a b c 

--------------------------------------------------------------------------------
-- Right Euclidean
-- R a b, R a c |- R b c
--------------------------------------------------------------------------------

-- Unconstrained

class RightEuc (L : Logic P) (R : Rel P T) :=
  rightEuc : (a b c : T) -> (L |- R a b) -> (L |- R a c) -> (L |- R b c)

def rightEuc {L : Logic P} {R : Rel P T}
  [K : RightEuc L R] {a b c} := K.rightEuc a b c 

-- Constrained

class RightEucT (L : Logic P) (R : Rel P T) (C : T -> P)  :=
  rightEucT : (a b c : T) -> 
    (L |- C a) -> (L |- C b) -> (L |- C c) -> 
    (L |- R a b) -> (L |- R a c) -> (L |- R b c)

instance iRightEucOfRightEucT {L : Logic P} {R : Rel P T} {C}
  [K : RightEuc L R] : RightEucT L R C 
  := {rightEucT := fun a b c _ _ _ => K.rightEuc a b c}

def rightEucT {L : Logic P} {R : Rel P T} {C} 
  [K : RightEucT L R C] {a b c} := K.rightEucT a b c 

--------------------------------------------------------------------------------
-- Join
--------------------------------------------------------------------------------

-- R a c, R b d, R c d |- R a b

class RelJoinT (L : Logic P) (R : Rel P T) (C : T -> P) :=
  relJoinT : (a b c d : T) -> 
    (L |- C a) -> (L |- C b) -> (L |- C c) -> (L |- C d) ->
    (L |- R a c) -> (L |- R b d) -> (L |- R c d) -> (L |- R a b)

def relJoinT {L : Logic P} {R : Rel P T} {C} 
  [K : RelJoinT L R C] {a b c d} := K.relJoinT a b c d

-- R c d, R a c, R b d |- R a b

def relJoinT' {L : Logic P} {R : Rel P T} {C} [K : RelJoinT L R C] {a b c d}
  (Ca Cb Cc Cd Rcd Rac Rbd) := K.relJoinT a b c d Ca Cb Cc Cd Rac Rbd Rcd

end Gaea.Logic