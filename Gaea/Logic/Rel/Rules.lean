import Gaea.Function
import Gaea.Logic.Rel.Type
import Gaea.Logic.Judgment
import Gaea.Logic.Rules

namespace Gaea.Logic

universes u v
variable {P : Sort u} {T : Sort v}

--------------------------------------------------------------------------------
-- Reflexivity
-- a -> (R a a)
--------------------------------------------------------------------------------

-- Unconstrained
class Refl (L : Logic P) (R : Rel P T) :=
  refl : (a : T) -> (L |- R a a)

instance iReflOfLRefl {L : Logic P} {F : Binar P}
  [K : LRefl L F] : Refl L F := {refl := K.lRefl}

instance iLReflOfRefl {L : Logic P} {F : Binar P}
  [K : Refl L F] : LRefl L F := {lRefl := K.refl}

def refl {L : Logic P} {R : Rel P T}
  [K : Refl L R] := K.refl

def refl' {L : Logic P} {R : Rel P T}
  [K : Refl L R] {a} := K.refl a

-- Constrained
class ReflT (L : Logic P) (R : Rel P T) (C : T -> P) :=
  reflT : (a : T) -> (L |- C a) -> (L |- R a a)

instance iReflOfReflT {L : Logic P} {R : Rel P T} {C : T -> P}
  [K : Refl L R] : ReflT L R C := {reflT := fun a _ => K.refl a}

def reflT 
  {L : Logic P} {R : Rel P T} {C : T -> P} 
  [K : ReflT L R C] {a} := K.reflT a

--------------------------------------------------------------------------------
-- Symmetry
-- (R a b) -> (R b a)
--------------------------------------------------------------------------------

-- Unconstrained
class Symm (L : Logic P) (R : Rel P T) :=
  symm : (a b : T) -> (L |- R a b) -> (L |- R b a)

instance iSymmOfLSymm {L : Logic P} {F : Binar P}
  [K : LSymm L F] : Symm L F := {symm := K.lSymm}

instance iLSymmOfSymm {L : Logic P} {F : Binar P}
  [K : Symm L F] : LSymm L F := {lSymm := K.symm}

def symm {L : Logic P} {R : Rel P T}
  [K : Symm L R] {a b} := K.symm a b

-- Constrained
class SymmT (L : Logic P) (R : Rel P T) (C : T -> P)  :=
  symmT : (a b : T) -> (L |- C a) -> (L |- C b) ->
    (L |- R a b) -> (L |- R b a)

instance iSymmOfSymmT {L : Logic P} {R : Rel P T} {C : T -> P}
  [K : Symm L R] : SymmT L R C := {symmT := fun a b _ _ => K.symm a b}

def symmT {L : Logic P} {R : Rel P T} {C : T -> P} 
  [K : SymmT L R C] {a b} := K.symmT a b 

--------------------------------------------------------------------------------
-- Transitivity
-- (R a b) /\ (R b c) -> (R a c)
--------------------------------------------------------------------------------

-- Unconstrained
class Trans (L : Logic P) (R : Rel P T) :=
  trans : (a b c : T) -> (L |- R a b) -> (L |- R b c) -> (L |- R a c)

instance iTransOfLTrans {L : Logic P} {F : Binar P}
  [K : LTrans L F] : Trans L F := {trans := K.lTrans}

instance iLTransOfTrans {L : Logic P} {F : Binar P}
  [K : Trans L F] : LTrans L F := {lTrans := K.trans}

def trans {L : Logic P} {R : Rel P T}
  [K : Trans L R] {a b c} := K.trans a b c 

def trans' {L : Logic P} {R : Rel P T}
  [K : Trans L R] {b a c} := K.trans b a c 

-- Constrained
class TransT (L : Logic P) (R : Rel P T) (C : T -> P) :=
  transT : (a b c : T) -> 
    (L |- C a) -> (L |- C b) -> (L |- C c) -> 
    (L |- R a b) -> (L |- R b c) -> (L |- R a c)

instance iTransOfTransT {L : Logic P} {R : Rel P T} {C : T -> P}
  [K : Trans L R] : TransT L R C 
  := {transT := fun a b c _ _ _ => K.trans a b c}

def transT {L : Logic P} {R : Rel P T} {C : T -> P} 
  [K : TransT L R C] {a b c : T} := K.transT a b c 

def transT' {L : Logic P} {R : Rel P T} {C : T -> P} 
  [K : TransT L R C] {b a c : T} (Cb : L |- C b) (Ca : L |- C a) (Cc : L |- C c)  
  := K.transT a b c Ca Cb Cc

--------------------------------------------------------------------------------
-- Join
--------------------------------------------------------------------------------

-- (R x a) /\ (R y b) /\ (R a b) -> (R x y)

class RelJoinT (L : Logic P) (R : Rel P T) (C : T -> P) :=
  relJoinT : (x y a b : T) -> 
    (L |- C x) -> (L |- C y) -> (L |- C a) -> (L |- C b) ->
    (L |- R x a) -> (L |- R y b) -> (L |- R a b) -> (L |- R x y)

def relJoinT {L : Logic P} {R : Rel P T} {C : T -> P} 
  [K : RelJoinT L R C] {x y a b} := K.relJoinT x y a b 

-- (R a b) /\ (R x a) /\ (R y b) -> (R x y)

def relJoinT' {L : Logic P} {R : Rel P T} {C : T -> P} 
  [K : RelJoinT L R C] {a b x y : T}
  := fun Ca Cb Cx Cy Rab Rxa Ryb => K.relJoinT x y a b Cx Cy Ca Cb Rxa Ryb Rab

--------------------------------------------------------------------------------
-- Euclideaness
--------------------------------------------------------------------------------

-- Left Eucldean
-- (R b a) /\ (R c a) -> (R b c)

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

instance iLeftEucOfLeftEucT {L : Logic P} {R : Rel P T} {C : T -> P}
  [K : LeftEuc L R] : LeftEucT L R C 
  := {leftEucT := fun a b c _ _ _ => K.leftEuc a b c}

def leftEucT {L : Logic P} {R : Rel P T} {C : T -> P} 
  [K : LeftEucT L R C] {a b c} := K.leftEucT a b c 

-- Right Euclidean
-- (a = b) /\ (a = c) -> (b = c)

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

instance iRightEucOfRightEucT {L : Logic P} {R : Rel P T} {C : T -> P}
  [K : RightEuc L R] : RightEucT L R C 
  := {rightEucT := fun a b c _ _ _ => K.rightEuc a b c}

def rightEucT {L : Logic P} {R : Rel P T} {C : T -> P} 
  [K : RightEucT L R C] {a b c} := K.rightEucT a b c 

--------------------------------------------------------------------------------
-- Predicate Substitution
-- R a b -> (P a -> P b)
--------------------------------------------------------------------------------

class PSubst (L : Logic P) (R : Rel P T) (F : T -> P) :=
  pSubst : (a b : T) -> (L |- R a b) -> (L |- F a) -> (L |- F b)

class PredSubst (L : Logic P) (R : Rel P T) :=
  predSubst : (F : T -> P) -> (a b : T) -> 
    (L |- R a b) -> (L |- F a) -> (L |- F b)

instance iPSubstOfPredSubst {L : Logic P} {R : Rel P T}
  [K : PredSubst L R] {F : T -> P} : PSubst L R F := {pSubst := K.predSubst F}

def predSubst {L : Logic P} {R : Rel P T}
  (F : T -> P) {a b} [K : PSubst L R F] := K.pSubst a b

def predSubst' {L : Logic P} {R : Rel P T}
  {F : T -> P} {a b} [K : PSubst L R F] := K.pSubst a b

--------------------------------------------------------------------------------
-- Function Substitution
-- (R a b) -> (R (f a) (f b))
--------------------------------------------------------------------------------

class FSubst (L : Logic P) (R : Rel P T) (f : Unar T) :=
  fSubst : (a b : T) -> (L |- R a b) -> (L |- R (f a) (f b))

class FunSubst (L : Logic P) (R : Rel P T) :=
  funSubst : (f : Unar T) -> (a b : T) -> (L |- R a b) -> (L |- R (f a) (f b))

instance iFSubstOfFunSubst {L : Logic P} {R : Rel P T}
  [K : FunSubst L R] {f : Unar T} : FSubst L R f := {fSubst := K.funSubst f}

def funSubst {L : Logic P} {R : Rel P T}
  (f) {a b} [K : FSubst L R f] := K.fSubst a b

def funSubst' {L : Logic P} {R : Rel P T}
  {f} {a b} [K : FSubst L R f] := K.fSubst a b

end Gaea.Logic