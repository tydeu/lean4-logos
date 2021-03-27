import Gaea.Logic.Notation
import Gaea.Logic.Rules

namespace Gaea.Logic

universes u v
variable {P : Sort u} {T : Sort v}

--------------------------------------------------------------------------------
-- Reflexivity
-- a -> (R a a)
--------------------------------------------------------------------------------

-- Unconstrained
class Refl (L : Logic P) (R : T -> T -> P) :=
  refl : (a : T) -> (L |- R a a)

instance iReflOfLRefl {L : Logic P} {F : P -> P -> P}
  [K : LRefl L F] : Refl L F := {refl := K.lRefl}

instance iLReflOfRefl {L : Logic P} {F : P -> P -> P}
  [K : Refl L F] : LRefl L F := {lRefl := K.refl}

def refl {L : Logic P} {R : T -> T -> P}
  [K : Refl L R] := K.refl

def refl' {L : Logic P} {R : T -> T -> P}
  [K : Refl L R] {a : T} := K.refl

-- Constrained
class MemRefl (L : Logic P) (R : T -> T -> P) (C : T -> P) :=
  memRefl : (a : T) -> (L |- C a) -> (L |- R a a)

instance iReflOfMemRefl {L : Logic P} {R : T -> T -> P} {C : T -> P}
  [K : Refl L R] : MemRefl L R C := {memRefl := fun a _ => K.refl a}

def memRefl 
  {L : Logic P} {R : T -> T -> P} {C : T -> P} 
  [K : MemRefl L R C] {a : T} := K.memRefl a

--------------------------------------------------------------------------------
-- Symmetry
-- (R a b) -> (R b a)
--------------------------------------------------------------------------------

-- Unconstrained
class Symm (L : Logic P) (R : T -> T -> P) :=
  symm : (a b : T) -> (L |- R a b) -> (L |- R b a)

instance iSymmOfLSymm {L : Logic P} {F : P -> P -> P}
  [K : LSymm L F] : Symm L F := {symm := K.lSymm}

instance iLSymmOfSymm {L : Logic P} {F : P -> P -> P}
  [K : Symm L F] : LSymm L F := {lSymm := K.symm}

def symm {L : Logic P} {R : T -> T -> P}
  [K : Symm L R] {a b : T} := K.symm a b

-- Constrained
class MemSymm (L : Logic P) (R : T -> T -> P) (C : T -> P)  :=
  memSymm : (a b : T) -> (L |- C a) -> (L |- C b) ->
    (L |- R a b) -> (L |- R b a)

instance iMemSymmOfSymm {L : Logic P} {R : T -> T -> P} {C : T -> P}
  [K : Symm L R] : MemSymm L R C := {memSymm := fun a b _ _ => K.symm a b}

def memSymm {L : Logic P} {R : T -> T -> P} {C : T -> P} 
  [K : MemSymm L R C] {a b : T} := K.memSymm a b 

--------------------------------------------------------------------------------
-- Transitivity
-- (R a b) /\ (R b c) -> (R a c)
--------------------------------------------------------------------------------

-- Unconstrained
class Trans (L : Logic P) (R : T -> T -> P) :=
  trans : (a b c : T) -> (L |- R a b) -> (L |- R b c) -> (L |- R a c)

instance iTransOfLTrans {L : Logic P} {F : P -> P -> P}
  [K : LTrans L F] : Trans L F := {trans := K.lTrans}

instance iLTransOfTrans {L : Logic P} {F : P -> P -> P}
  [K : Trans L F] : LTrans L F := {lTrans := K.trans}

def trans {L : Logic P} {R : T -> T -> P}
  [K : Trans L R] {a b c : T} := K.trans a b c 

def trans' {L : Logic P} {R : T -> T -> P}
  [K : Trans L R] {b a c : T} := K.trans b a c 

-- Constrained
class MemTrans (L : Logic P) (R : T -> T -> P) (C : T -> P) :=
  memTrans : (a b c : T) -> 
    (L |- C a) -> (L |- C b) -> (L |- C c) -> 
    (L |- R a b) -> (L |- R b c) -> (L |- R a c)

instance iMemTransOfTrans {L : Logic P} {R : T -> T -> P} {C : T -> P}
  [K : Trans L R] : MemTrans L R C 
  := {memTrans := fun a b c _ _ _ => K.trans a b c}

def memTrans {L : Logic P} {R : T -> T -> P} {C : T -> P} 
  [K : MemTrans L R C] {a b c : T} := K.memTrans a b c 

def memTrans' {L : Logic P} {R : T -> T -> P} {C : T -> P} 
  [K : MemTrans L R C] {b a c : T} (Cb : L |- C b) (Ca : L |- C a) (Cc : L |- C c)  
  := K.memTrans a b c Ca Cb Cc

--------------------------------------------------------------------------------
-- Join
--------------------------------------------------------------------------------

-- (R x a) /\ (R y b) /\ (R a b) -> (R x y)

class RelMemJoin (L : Logic P) (R : T -> T -> P) (C : T -> P) :=
  relMemJoin : (x y a b : T) -> 
    (L |- C x) -> (L |- C y) -> (L |- C a) -> (L |- C b) ->
    (L |- R x a) -> (L |- R y b) -> (L |- R a b) -> (L |- R x y)

def relMemJoin {L : Logic P} {R : T -> T -> P} {C : T -> P} 
  [K : RelMemJoin L R C] {x y a b : T} := K.relMemJoin x y a b 

-- (R a b) /\ (R x a) /\ (R y b) -> (R x y)

def relMemJoin' {L : Logic P} {R : T -> T -> P} {C : T -> P} 
  [K : RelMemJoin L R C] {a b x y : T}
  := fun Ca Cb Cx Cy Rab Rxa Ryb => K.relMemJoin x y a b Cx Cy Ca Cb Rxa Ryb Rab

--------------------------------------------------------------------------------
-- Euclideaness
--------------------------------------------------------------------------------

-- Left Eucldean
-- (R b a) /\ (R c a) -> (R b c)

-- Unconstrained
class LeftEuc (L : Logic P) (R : T -> T -> P) :=
  leftEuc : (a b c : T) -> (L |- R b a) -> (L |- R c a) -> (L |- R b c)

def leftEuc {L : Logic P} {R : T -> T -> P}
  [K : LeftEuc L R] {a b c : T} := K.leftEuc a b c 

-- Constrained
class MemLeftEuc (L : Logic P) (R : T -> T -> P) (C : T -> P) :=
  memLeftEuc : (a b c : T) -> 
    (L |- C a) -> (L |- C b) -> (L |- C c) -> 
    (L |- R b a) -> (L |- R c a) -> (L |- R b c)

instance iMemLeftEucOfLeftEuc {L : Logic P} {R : T -> T -> P} {C : T -> P}
  [K : LeftEuc L R] : MemLeftEuc L R C 
  := {memLeftEuc := fun a b c _ _ _ => K.leftEuc a b c}

def memLeftEuc {L : Logic P} {R : T -> T -> P} {C : T -> P} 
  [K : MemLeftEuc L R C] {a b c : T} := K.memLeftEuc a b c 

-- Right Euclidean
-- (a = b) /\ (a = c) -> (b = c)

-- Unconstrained
class RightEuc (L : Logic P) (R : T -> T -> P) :=
  rightEuc : (a b c : T) -> (L |- R a b) -> (L |- R a c) -> (L |- R b c)

def rightEuc {L : Logic P} {R : T -> T -> P}
  [K : RightEuc L R] {a b c : T} := K.rightEuc a b c 

-- Constrained
class MemRightEuc (L : Logic P) (R : T -> T -> P) (C : T -> P)  :=
  memRightEuc : (a b c : T) -> 
    (L |- C a) -> (L |- C b) -> (L |- C c) -> 
    (L |- R a b) -> (L |- R a c) -> (L |- R b c)

instance iMemRightEucOfRightEuc {L : Logic P} {R : T -> T -> P} {C : T -> P}
  [K : RightEuc L R] : MemRightEuc L R C 
  := {memRightEuc := fun a b c _ _ _ => K.rightEuc a b c}

def memRightEuc {L : Logic P} {R : T -> T -> P} {C : T -> P} 
  [K : MemRightEuc L R C] {a b c : T} := K.memRightEuc a b c 

--------------------------------------------------------------------------------
-- Predicate Substitution
-- R a b -> (P a -> P b)
--------------------------------------------------------------------------------

class PredSubst (L : Logic P) (R : T -> T -> P) :=
  predSubst : (a b : T) -> (F : T -> P) -> 
    (L |- R a b) -> (L |- F a) -> (L |- F b)

def predSubst {L : Logic P} {R : T -> T -> P}
  [K : PredSubst L R] {a b : T} := K.predSubst a b

def predSubst' {L : Logic P} {R : T -> T -> P}
  [K : PredSubst L R] {a b : T} {F : T -> P} := K.predSubst a b F

--------------------------------------------------------------------------------
-- Function Substitution
-- (R a b) -> (R (f a) (f b))
--------------------------------------------------------------------------------

class FunSubst (L : Logic P) (R : T -> T -> P) :=
  funSubst : (a b : T) -> (f : T -> T) -> 
    (L |- R a b) -> (L |- R (f a) (f b))

def funSubst {L : Logic P} {R : T -> T -> P}
  [K : FunSubst L R] {a b : T} := K.funSubst a b

def funSubst' {L : Logic P} {R : T -> T -> P}
  [K : FunSubst L R] {a b : T} {f : T -> T} := K.funSubst a b f

end Gaea.Logic