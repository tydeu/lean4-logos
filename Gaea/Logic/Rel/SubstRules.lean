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

def psubst {L : Logic P} {R : Rel P T}
  {F} [K : PSubst L R F] {a b} := K.toFun a b

--------------------------------------------------------------------------------
-- Function Substitution
-- R a b |- R (f a) (f b)
--------------------------------------------------------------------------------

-- Unconstrained

class FunSubst (L : Logic P) (R : Rel P T) :=
  toFun : (f : Unar T) -> (a b : T) -> (L |- R a b) -> (L |- R (f a) (f b))

-- Constrained

class FunSubstT (L : Logic P) (R : Rel P T) (C : T -> P) :=
  toFun : (f : Unar T) -> (a b : T) -> 
    (L |- C a) -> (L |- C b) -> (L |- R a b) -> (L |- R (f a) (f b))

instance iFunSubstTOfFunSubst {L : Logic P} 
  {R : Rel P T} {C : T -> P} [K : FunSubst L R] : FunSubstT L R C := 
  {toFun := fun f a b _ _  => K.toFun f a b}

--------------------------------------------------------------------------------
-- Unar Application
-- R a b |- R (f a) (f b)
--------------------------------------------------------------------------------

-- Unconstrained

class FApply (L : Logic P) (R : Rel P T) (f : Unar T) :=
  toFun : (a b : T) -> (L |- R a b) -> (L |- R (f a) (f b))

instance iFApplyOfFunSubst {L : Logic P} {R : Rel P T}
  [K : FunSubst L R] {f : Unar T} : FApply L R f := {toFun := K.toFun f}

def fapply {L : Logic P} {R : Rel P T}
  {f} [K : FApply L R f] {a b} := K.toFun a b

-- Constrained

class FApplyT (L : Logic P) (R : Rel P T) (C : T -> P) (f : Unar T) :=
  toFun : (a b : T) -> (L |- C a) -> (L |- C b) -> 
    (L |- R a b) -> (L |- R (f a) (f b))

instance iFApplyTOfFApply {L : Logic P} 
  {R : Rel P T} {C : T -> P} {f} [K : FApply L R f]  : FApplyT L R C f := 
  {toFun := fun a b _ _  => K.toFun a b}

instance iFApplyTOfFunSubstT {L : Logic P} 
  {R : Rel P T} {C} [K : FunSubstT L R C] {f : Unar T} : FApplyT L R C f := 
  {toFun := K.toFun f}

def fapplyT {L : Logic P} {R : Rel P T} {C}
  {f} [K : FApplyT L R C f] {a b} := K.toFun a b

--------------------------------------------------------------------------------
-- Unar Cancellation
-- R (f a) (f b) |- R a b
--------------------------------------------------------------------------------

-- Unconstrained

class FCancel (L : Logic P) (R : Rel P T) (f : Unar T) :=
  toFun : (a b : T) -> (L |- R (f a) (f b)) -> (L |- R a b)

def fcancel {L : Logic P} {R : Rel P T}
  {f} [K : FCancel L R f] {a b} := K.toFun a b

-- Constrained

class FCancelT (L : Logic P) (R : Rel P T) (C : T -> P) (f : Unar T) :=
  toFun : (a b : T) -> (L |- C a) -> (L |- C b) -> 
    (L |- R (f a) (f b)) -> (L |- R a b)

instance iFCancelTOfFCancel {L : Logic P} 
  {R : Rel P T} {C : T -> P} {f} [K : FCancel L R f]  : FCancelT L R C f := 
  {toFun := fun a b _ _  => K.toFun a b}

def fcancelT {L : Logic P} {R : Rel P T} {C}
  {f} [K : FCancelT L R C f] {a b} := K.toFun a b

--------------------------------------------------------------------------------
-- Binar Application
--------------------------------------------------------------------------------

-- Left Apply
-- R b c |- R (f a b) (f a c)

-- Unconstrained

class LeftApply (L : Logic P) (R : Rel P T) (f : Binar T) :=
  toFun : (a b c : T) -> 
    (L |- R b c) -> (L |- R (f a b) (f a c))

def leftApply {L : Logic P} {R : Rel P T} {f}
  [K : LeftApply L R f] {a b c} := K.toFun a b c

-- Constrained 

class LeftApplyT (L : Logic P) (R : Rel P T) (C : T -> P) (f : Binar T) :=
  toFun : (a b c : T) -> 
    (L |- C a) -> (L |- C b) -> (L |- C c) ->
    (L |- R b c) -> (L |- R (f a b) (f a c))

def leftApplyT {L : Logic P} {R : Rel P T} {C f}
  [K : LeftApplyT L R C f] {a b c} := K.toFun a b c

-- Right Apply
-- R b c |- R (f b a) (f c a)

-- Unconstrained

class RightApply (L : Logic P) (R : Rel P T) (f : Binar T) :=
  toFun : (a b c : T) ->
    (L |- R b c) -> (L |- R (f b a) (f c a))

def rightApply {L : Logic P} {R : Rel P T} {f}
  [K : RightApply L R f] {a b c} := K.toFun a b c

-- Constrained

class RightApplyT (L : Logic P) (R : Rel P T) (C : T -> P) (f : Binar T) :=
  toFun : (a b c : T) -> 
    (L |- C a) -> (L |- C b) -> (L |- C c) ->
    (L |- R b c) -> (L |- R (f b a) (f c a))

def rightApplyT {L : Logic P} {R : Rel P T} {C f}
  [K : RightApplyT L R C f] {a b c} := K.toFun a b c

--------------------------------------------------------------------------------
-- Binar Cancellation
--------------------------------------------------------------------------------

-- Left Cancel
-- R (f a b) (f a c) |- R a b

class LeftCancel (L : Logic P) (R : Rel P T) (f : Binar T) :=
  toFun : (a b c : T) -> (L |- R (f a b) (f a c)) -> (L |- R b c) 

def leftCancel {L : Logic P} {R : Rel P T} {f}
  [K : LeftCancel L R f] {a b c} := K.toFun a b c

-- Right Cancel
-- R (f b a) (f c a) |- R a b

class RightCancel (L : Logic P) (R : Rel P T) (f : Binar T) :=
  toFun : (a b c : T) -> (L |- R (f b a) (f c a)) -> (L |- R b c) 

def rightCancel {L : Logic P} {R : Rel P T} {f}
  [K : RightCancel L R f] {a b c} := K.toFun a b c

