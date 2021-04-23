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
  toFun : (a : T) -> (L |- R a a)

def refl {L : Logic P} {R : Rel P T}
  [K : Refl L R] := K.toFun

def rfl {L : Logic P} {R : Rel P T}
  [K : Refl L R] {a} := K.toFun a

-- Constrained

class ReflT (L : Logic P) (R : Rel P T) (C : T -> P) :=
  toFun : (a : T) -> (L |- C a) -> (L |- R a a)

instance iReflOfReflT {L : Logic P} {R : Rel P T} {C}
  [K : Refl L R] : ReflT L R C := {toFun := fun a _ => K.toFun a}

def reflT {L : Logic P} {R : Rel P T} {C} 
  [K : ReflT L R C] {a} := K.toFun a

--------------------------------------------------------------------------------
-- Symmetry
-- R a b |- R b a
--------------------------------------------------------------------------------

-- Unconstrained

class Symm (L : Logic P) (R : Rel P T) :=
  toFun : (a b : T) -> (L |- R a b) -> (L |- R b a)

def symm {L : Logic P} {R : Rel P T}
  [K : Symm L R] {a b} := K.toFun a b

-- Constrained

class SymmT (L : Logic P) (R : Rel P T) (C : T -> P)  :=
  toFun : (a b : T) -> (L |- C a) -> (L |- C b) ->
    (L |- R a b) -> (L |- R b a)

instance iSymmOfSymmT {L : Logic P} {R : Rel P T} {C}
  [K : Symm L R] : SymmT L R C := {toFun := fun a b _ _ => K.toFun a b}

def symmT {L : Logic P} {R : Rel P T} {C} 
  [K : SymmT L R C] {a b} := K.toFun a b 

--------------------------------------------------------------------------------
-- Transitivity
-- R a b, R b c |- R a c
--------------------------------------------------------------------------------

-- Unconstrained

class Trans (L : Logic P) (R : Rel P T) :=
  toFun : (a b c : T) -> (L |- R a b) -> (L |- R b c) -> (L |- R a c)

def trans {L : Logic P} {R : Rel P T}
  [K : Trans L R] {a b c} := K.toFun a b c 

def trans' {L : Logic P} {R : Rel P T}
  [K : Trans L R] (b) {a c} := K.toFun a b c 

-- Constrained

class TransT (L : Logic P) (R : Rel P T) (C : T -> P) :=
  toFun : (a b c : T) -> 
    (L |- C a) -> (L |- C b) -> (L |- C c) -> 
    (L |- R a b) -> (L |- R b c) -> (L |- R a c)

instance iTransOfTransT {L : Logic P} {R : Rel P T} {C}
  [K : Trans L R] : TransT L R C 
  := {toFun := fun a b c _ _ _ => K.toFun a b c}

def transT {L : Logic P} {R : Rel P T} {C} 
  [K : TransT L R C] {a b c : T} := K.toFun a b c 

def transT' {L : Logic P} {R : Rel P T} {C} 
  [K : TransT L R C] {b a c Cb Ca Cc} := K.toFun a b c Ca Cb Cc

--------------------------------------------------------------------------------
-- Left Euclidean
-- R b a, R c a |- R b c
--------------------------------------------------------------------------------

-- Unconstrained

class LeftEuc (L : Logic P) (R : Rel P T) :=
  toFun : (a b c : T) -> (L |- R b a) -> (L |- R c a) -> (L |- R b c)

def leftEuc {L : Logic P} {R : Rel P T}
  [K : LeftEuc L R] {a b c} := K.toFun a b c 

-- Constrained

class LeftEucT (L : Logic P) (R : Rel P T) (C : T -> P) :=
  toFun : (a b c : T) -> 
    (L |- C a) -> (L |- C b) -> (L |- C c) -> 
    (L |- R b a) -> (L |- R c a) -> (L |- R b c)

instance iLeftEucOfLeftEucT {L : Logic P} {R : Rel P T} {C}
  [K : LeftEuc L R] : LeftEucT L R C 
  := {toFun := fun a b c _ _ _ => K.toFun a b c}

def leftEucT {L : Logic P} {R : Rel P T} {C} 
  [K : LeftEucT L R C] {a b c} := K.toFun a b c 

--------------------------------------------------------------------------------
-- Right Euclidean
-- R a b, R a c |- R b c
--------------------------------------------------------------------------------

-- Unconstrained

class RightEuc (L : Logic P) (R : Rel P T) :=
  toFun : (a b c : T) -> (L |- R a b) -> (L |- R a c) -> (L |- R b c)

def rightEuc {L : Logic P} {R : Rel P T}
  [K : RightEuc L R] {a b c} := K.toFun a b c 

-- Constrained

class RightEucT (L : Logic P) (R : Rel P T) (C : T -> P)  :=
  toFun : (a b c : T) -> 
    (L |- C a) -> (L |- C b) -> (L |- C c) -> 
    (L |- R a b) -> (L |- R a c) -> (L |- R b c)

instance iRightEucOfRightEucT {L : Logic P} {R : Rel P T} {C}
  [K : RightEuc L R] : RightEucT L R C 
  := {toFun := fun a b c _ _ _ => K.toFun a b c}

def rightEucT {L : Logic P} {R : Rel P T} {C} 
  [K : RightEucT L R C] {a b c} := K.toFun a b c 

--------------------------------------------------------------------------------
-- Join
--------------------------------------------------------------------------------

-- R a c, R b d, R c d |- R a b

class RelJoinT (L : Logic P) (R : Rel P T) (C : T -> P) :=
  toFun : (a b c d : T) -> 
    (L |- C a) -> (L |- C b) -> (L |- C c) -> (L |- C d) ->
    (L |- R a c) -> (L |- R b d) -> (L |- R c d) -> (L |- R a b)

def relJoinT {L : Logic P} {R : Rel P T} {C} 
  [K : RelJoinT L R C] {a b c d} := K.toFun a b c d

-- R c d, R a c, R b d |- R a b

def relJoinT' {L : Logic P} {R : Rel P T} {C} [K : RelJoinT L R C] {a b c d}
  (Ca Cb Cc Cd Rcd Rac Rbd) := K.toFun a b c d Ca Cb Cc Cd Rac Rbd Rcd

end Gaea.Logic