import Gaea.Logic.Judgment
import Gaea.FunTypes
import Gaea.FunTypes

universes u v
variable {P : Sort u} {T : Sort v}

namespace Gaea

--------------------------------------------------------------------------------
-- Predicate Substitution
-- (|- R a b) -> ((|- F a) -> (|- F b))
--------------------------------------------------------------------------------

class PSubst (L : Logic P) (R : Rel P T) (F : Pred P T) :=
  toFun : (a b : T) -> (L |- R a b) -> (L |- F a) -> (L |- F b)

class PredSubst (L : Logic P) (R : Rel P T) :=
  toFun : (F : Pred P T) -> (a b : T) -> 
    (L |- R a b) -> (L |- F a) -> (L |- F b)

instance iPSubstOfPredSubst {L : Logic P} {R : Rel P T}
  [K : PredSubst L R] {F} : PSubst L R F := {toFun := K.toFun F}

def predSubst {L : Logic P} {R : Rel P T}
  {F} [K : PSubst L R F] {a b} := K.toFun a b

def predSubst' {L : Logic P} {R : Rel P T}
  (F) [K : PSubst L R F] {a b} := K.toFun a b

--------------------------------------------------------------------------------
-- Function Substitution
-- R a b |- R (f a) (f b)
--------------------------------------------------------------------------------

-- Unconstrained

class FSubst (L : Logic P) (R : Rel P T) (f : Unar T) :=
  toFun : (a b : T) -> (L |- R a b) -> (L |- R (f a) (f b))

class FunSubst (L : Logic P) (R : Rel P T) :=
  toFun : (f : Unar T) -> (a b : T) -> (L |- R a b) -> (L |- R (f a) (f b))

instance iFSubstOfFunSubst {L : Logic P} {R : Rel P T}
  [K : FunSubst L R] {f : Unar T} : FSubst L R f := {toFun := K.toFun f}

def funSubst {L : Logic P} {R : Rel P T}
  {f} [K : FSubst L R f] {a b} := K.toFun a b

-- Constrained

class FSubstT (L : Logic P) (R : Rel P T) (C : T -> P) (f : Unar T) :=
  toFun : (a b : T) -> (L |- C a) -> (L |- C b) -> 
    (L |- R a b) -> (L |- R (f a) (f b))

class FunSubstT (L : Logic P) (R : Rel P T) (C : T -> P) :=
  toFun : (f : Unar T) -> (a b : T) -> 
    (L |- C a) -> (L |- C b) -> (L |- R a b) -> (L |- R (f a) (f b))

instance iFSubstTOfFunSubstT {L : Logic P} 
  {R : Rel P T} {C} [K : FunSubstT L R C] {f : Unar T} : FSubstT L R C f := 
  {toFun := K.toFun f}

instance iFSubstTOfFSubst {L : Logic P} 
  {R : Rel P T} {C : T -> P} {f} [K : FSubst L R f]  : FSubstT L R C f := 
  {toFun := fun a b _ _  => K.toFun a b}

instance iFunSubstTOfFunSubst {L : Logic P} 
  {R : Rel P T} {C : T -> P} [K : FunSubst L R] : FunSubstT L R C := 
  {toFun := fun f a b _ _  => K.toFun f a b}

def funSubstT {L : Logic P} {R : Rel P T} {C}
  {f} [K : FSubstT L R C f] {a b} := K.toFun a b

--------------------------------------------------------------------------------
-- Binar Substitution
--------------------------------------------------------------------------------

-- Left Reflection / Right Substitution
-- R a b |- R (f c a) (f c b)

-- Constrained for a given function
class LeftReflT (L : Logic P) (R : Rel P T) (C : T -> P) (f : Binar T) :=
  toFun : (a b c : T) -> 
    (L |- C a) -> (L |- C b) -> (L |- C c) ->
    (L |- R b c) -> (L |- R (f a b) (f a c))

def leftReflT {L : Logic P} {R : Rel P T} {C f}
  [K : LeftReflT L R C f] {a b c} := K.toFun a b c

-- Right Reflection / Left Substitution
-- R a b |- R (f a c) (f b c)

-- Constrained for a given function
class RightReflT (L : Logic P) (R : Rel P T) (C : T -> P) (f : Binar T) :=
  toFun : (a b c : T) -> 
    (L |- C a) -> (L |- C b) -> (L |- C c) ->
    (L |- R b c) -> (L |- R (f b a) (f c a))

def rightReflT {L : Logic P} {R : Rel P T} {C f}
  [K : RightReflT L R C f] {a b c} := K.toFun a b c
