import Gaea.Logic.Logic
import Gaea.Logic.Notation

universes u v w

namespace Gaea.Logic

--------------------------------------------------------------------------------
-- Reflexivity
-- a -> (R a a)
--------------------------------------------------------------------------------

-- Unconstrained
class Refl {P : Sort u} {T : Sort v} (L : Logic P) (R : T -> T -> P) :=
  (refl : (a : T) -> (L |- R a a))

def refl {P : Sort u} {T : Sort v} {L : Logic P} {R : T -> T -> P}
  [K : Refl L R] := K.refl

def refl' {P : Sort u} {T : Sort v} {L : Logic P} {R : T -> T -> P}
  [K : Refl L R] {a : T} := K.refl

-- Constrained
class MemRefl {P : Sort u} {T : Sort v} 
  (L : Logic P) (R : T -> T -> P) (C : T -> P) :=
  (memRefl : (a : T) -> (L |- C a) -> (L |- R a a))

instance {P : Sort u} {T : Sort v} {L : Logic P} {R : T -> T -> P} {C : T -> P}
  [K : Refl L R] : MemRefl L R C := {memRefl := fun a _ => K.refl a}

def memRefl {P : Sort u} {T : Sort v} 
  {L : Logic P} {R : T -> T -> P} {C : T -> P} 
  [K : MemRefl L R C] {a : T} := K.memRefl a

--------------------------------------------------------------------------------
-- Symmetry
-- (R a b) -> (R b a)
--------------------------------------------------------------------------------

-- Unconstrained
class Symm {P : Sort u} {T : Sort v} (L : Logic P) (R : T -> T -> P) :=
  (symm : (a b : T) -> (L |- R a b) -> (L |- R b a))

def symm {P : Sort u} {T : Sort v} {L : Logic P} {R : T -> T -> P}
  [K : Symm L R] {a b : T} := K.symm a b

-- Constrained
class MemSymm {P : Sort u} {T : Sort v} 
  (L : Logic P) (R : T -> T -> P) (C : T -> P)  :=
  (memSymm : (a b : T) -> 
    (L |- C a) -> (L |- C b) ->
    (L |- R a b) -> (L |- R b a))

instance {P : Sort u} {T : Sort v} {L : Logic P} {R : T -> T -> P} {C : T -> P}
  [K : Symm L R] : MemSymm L R C := {memSymm := fun a b _ _ => K.symm a b}

def memSymm {P : Sort u} {T : Sort v} 
  {L : Logic P} {R : T -> T -> P} {C : T -> P} 
  [K : MemSymm L R C] {a b : T} := K.memSymm a b 

--------------------------------------------------------------------------------
-- Transitivity
-- (R a b) /\ (R b c) -> (R a c)
--------------------------------------------------------------------------------

-- Unconstrained
class Trans {P : Sort u} {T : Sort v} (L : Logic P) (R : T -> T -> P) :=
  (trans : (a b c : T) -> (L |- R a b) -> (L |- R b c) -> (L |- R a c))

def trans {P : Sort u} {T : Sort v} {L : Logic P} {R : T -> T -> P}
  [K : Trans L R] {a b c : T} := K.trans a b c 

def trans' {P : Sort u} {T : Sort v} {L : Logic P} {R : T -> T -> P}
  [K : Trans L R] {b a c : T} := K.trans b a c 

-- Constrained
class MemTrans {P : Sort u} {T : Sort v} 
  (L : Logic P) (R : T -> T -> P) (C : T -> P) :=
  (memTrans : (a b c : T) -> 
    (L |- C a) -> (L |- C b) -> (L |- C c) -> 
    (L |- R a b) -> (L |- R b c) -> (L |- R a c))

instance {P : Sort u} {T : Sort v} {L : Logic P} {R : T -> T -> P} {C : T -> P}
  [K : Trans L R] : MemTrans L R C 
  := {memTrans := fun a b c _ _ _ => K.trans a b c}

def memTrans {P : Sort u} {T : Sort v} 
  {L : Logic P} {R : T -> T -> P} {C : T -> P} 
  [K : MemTrans L R C] {a b c : T} := K.memTrans a b c 

def memTrans' {P : Sort u} {T : Sort v} 
  {L : Logic P} {R : T -> T -> P} {C : T -> P} [K : MemTrans L R C] 
  {b a c : T} (Cb : L |- C b) (Ca : L |- C a) (Cc : L |- C c)  
  := K.memTrans a b c Ca Cb Cc

--------------------------------------------------------------------------------
-- Join
--------------------------------------------------------------------------------

-- (R x a) /\ (R y b) /\ (R a b) -> (R x y)

class RelMemJoin {P : Sort u} {T : Sort v} 
  (L : Logic P) (R : T -> T -> P) (C : T -> P) :=
  (relMemJoin : (x y a b : T) -> 
    (L |- C x) -> (L |- C y) -> (L |- C a) -> (L |- C b) ->
    (L |- R x a) -> (L |- R y b) -> (L |- R a b) -> (L |- R x y))

def relMemJoin {P : Sort u} {T : Sort v} 
  {L : Logic P} {R : T -> T -> P} {C : T -> P} 
  [K : RelMemJoin L R C] {x y a b : T} := K.relMemJoin x y a b 

-- (R a b) /\ (R x a) /\ (R y b) -> (R x y)

def relMemJoin' {P : Sort u} {T : Sort v} 
  {L : Logic P} {R : T -> T -> P} {C : T -> P} 
  [K : RelMemJoin L R C] {a b x y : T}
  := fun Ca Cb Cx Cy Rab Rxa Ryb => K.relMemJoin x y a b Cx Cy Ca Cb Rxa Ryb Rab

--------------------------------------------------------------------------------
-- Euclideaness
--------------------------------------------------------------------------------

-- Left Eucldean
-- (R b a) /\ (R c a) -> (R b c)

-- Unconstrained
class LeftEuc {P : Sort u} {T : Sort v} (L : Logic P) (R : T -> T -> P) :=
  (leftEuc : (a b c : T) ->
    (L |- R b a) -> (L |- R c a) -> (L |- R b c))

def leftEuc {P : Sort u} {T : Sort v} {L : Logic P} {R : T -> T -> P}
  [K : LeftEuc L R] {a b c : T} := K.leftEuc a b c 

-- Constrained
class MemLeftEuc {P : Sort u} {T : Sort v} 
  (L : Logic P) (R : T -> T -> P) (C : T -> P) :=
  (memLeftEuc : (a b c : T) -> 
    (L |- C a) -> (L |- C b) -> (L |- C c) -> 
    (L |- R b a) -> (L |- R c a) -> (L |- R b c))

instance {P : Sort u} {T : Sort v} {L : Logic P} {R : T -> T -> P} {C : T -> P}
  [K : LeftEuc L R] : MemLeftEuc L R C 
  := {memLeftEuc := fun a b c _ _ _ => K.leftEuc a b c}

def memLeftEuc {P : Sort u} {T : Sort v} 
  {L : Logic P} {R : T -> T -> P} {C : T -> P} 
  [K : MemLeftEuc L R C] {a b c : T} := K.memLeftEuc a b c 

-- Right Euclidean
-- (a = b) /\ (a = c) -> (b = c)

-- Unconstrained
class RightEuc {P : Sort u} {T : Sort v} (L : Logic P) (R : T -> T -> P) :=
  (rightEuc : (a b c : T) ->
    (L |- R a b) -> (L |- R a c) -> (L |- R b c))

def rightEuc {P : Sort u} {T : Sort v} {L : Logic P} {R : T -> T -> P}
  [K : RightEuc L R] {a b c : T} := K.rightEuc a b c 

-- Constrained
class MemRightEuc {P : Sort u} {T : Sort v} 
  (L : Logic P) (R : T -> T -> P) (C : T -> P)  :=
  (memRightEuc : (a b c : T) -> 
    (L |- C a) -> (L |- C b) -> (L |- C c) -> 
    (L |- R a b) -> (L |- R a c) -> (L |- R b c))

instance {P : Sort u} {T : Sort v} {L : Logic P} {R : T -> T -> P} {C : T -> P}
  [K : RightEuc L R] : MemRightEuc L R C 
  := {memRightEuc := fun a b c _ _ _ => K.rightEuc a b c}

def memRightEuc {P : Sort u} {T : Sort v} 
  {L : Logic P} {R : T -> T -> P} {C : T -> P} 
  [K : MemRightEuc L R C] {a b c : T} := K.memRightEuc a b c 

--------------------------------------------------------------------------------
-- Predicate Substitution
-- R a b -> (P a -> P b)
--------------------------------------------------------------------------------

class PredSubst {P : Sort u} {T : Sort v} (L : Logic P) (R : T -> T -> P) :=
  (predSubst : (a b : T) -> (F : T -> P) -> 
    (L |- R a b) -> (L |- F a) -> (L |- F b))

def predSubst {P : Sort u} {T : Sort v} {L : Logic P} {R : T -> T -> P}
  [K : PredSubst L R] {a b : T} := K.predSubst a b

def predSubst' {P : Sort u} {T : Sort v} {L : Logic P} {R : T -> T -> P}
  [K : PredSubst L R] {a b : T} {F : T -> P} := K.predSubst a b F

--------------------------------------------------------------------------------
-- Function Substitution
-- (R a b) -> (R (f a) (f b))
--------------------------------------------------------------------------------

class FunSubst {P : Sort u} {T : Sort v} (L : Logic P) (R : T -> T -> P) :=
  (funSubst : (a b : T) -> (f : T -> T) -> 
    (L |- R a b) -> (L |- R (f a) (f b)))

def funSubst {P : Sort u} {T : Sort v} {L : Logic P} {R : T -> T -> P}
  [K : FunSubst L R] {a b : T} := K.funSubst a b

def funSubst' {P : Sort u} {T : Sort v} {L : Logic P} {R : T -> T -> P}
  [K : FunSubst L R] {a b : T} {f : T -> T} := K.funSubst a b f

end Gaea.Logic