import Gaea.Logic.Fun.Types
import Gaea.Logic.Rel.Type
import Gaea.Logic.Judgment
import Gaea.Logic.Fun.Rules

universes u v
variable {P : Sort u} {T : Sort v}

namespace Gaea.Logic

--------------------------------------------------------------------------------
-- Predicate Substitution
-- (|- R a b) -> ((|- F a) -> (|- F b))
--------------------------------------------------------------------------------

class PSubst (L : Logic P) (R : Rel P T) (F : T -> P) :=
  pSubst : (a b : T) -> (L |- R a b) -> (L |- F a) -> (L |- F b)

class PredSubst (L : Logic P) (R : Rel P T) :=
  predSubst : (F : T -> P) -> (a b : T) -> 
    (L |- R a b) -> (L |- F a) -> (L |- F b)

instance iPSubstOfPredSubst {L : Logic P} {R : Rel P T}
  [K : PredSubst L R] {F} : PSubst L R F := {pSubst := K.predSubst F}

def predSubst {L : Logic P} {R : Rel P T}
  {F} [K : PSubst L R F] {a b} := K.pSubst a b

def predSubst' {L : Logic P} {R : Rel P T}
  (F) [K : PSubst L R F] {a b} := K.pSubst a b

--------------------------------------------------------------------------------
-- Function Substitution
-- R a b |- R (f a) (f b)
--------------------------------------------------------------------------------

-- Unconstrained

class FSubst (L : Logic P) (R : Rel P T) (f : Unar T) :=
  fSubst : (a b : T) -> (L |- R a b) -> (L |- R (f a) (f b))

class FunSubst (L : Logic P) (R : Rel P T) :=
  funSubst : (f : Unar T) -> (a b : T) -> (L |- R a b) -> (L |- R (f a) (f b))

instance iFSubstOfFunSubst {L : Logic P} {R : Rel P T}
  [K : FunSubst L R] {f : Unar T} : FSubst L R f := {fSubst := K.funSubst f}

def funSubst {L : Logic P} {R : Rel P T}
  {f} [K : FSubst L R f] {a b} := K.fSubst a b

-- Constrained

class FSubstT (L : Logic P) (R : Rel P T) (C : T -> P) (f : Unar T) :=
  fSubstT : (a b : T) -> (L |- C a) -> (L |- C b) -> 
    (L |- R a b) -> (L |- R (f a) (f b))

class FunSubstT (L : Logic P) (R : Rel P T) (C : T -> P) :=
  funSubstT : (f : Unar T) -> (a b : T) -> 
    (L |- C a) -> (L |- C b) -> (L |- R a b) -> (L |- R (f a) (f b))

instance iFSubstTOfFunSubstT {L : Logic P} 
  {R : Rel P T} {C} [K : FunSubstT L R C] {f : Unar T} : FSubstT L R C f := 
  {fSubstT := K.funSubstT f}

instance iFSubstTOfFSubst {L : Logic P} 
  {R : Rel P T} {C : T -> P} {f} [K : FSubst L R f]  : FSubstT L R C f := 
  {fSubstT := fun a b _ _  => K.fSubst a b}

instance iFunSubstTOfFunSubst {L : Logic P} 
  {R : Rel P T} {C : T -> P} [K : FunSubst L R] : FunSubstT L R C := 
  {funSubstT := fun f a b _ _  => K.funSubst f a b}

def funSubstT {L : Logic P} {R : Rel P T} {C}
  {f} [K : FSubstT L R C f] {a b} := K.fSubstT a b

--------------------------------------------------------------------------------
-- Binar Substitution
--------------------------------------------------------------------------------

-- Left Reflection / Right Substitution
-- R a b |- R (f c a) (f c b)

-- Constrained for a given function
class LeftReflT (L : Logic P) (R : Rel P T) (C : T -> P) (f : Binar T) :=
  leftReflT : (a b c : T) -> 
    (L |- C a) -> (L |- C b) -> (L |- C c) ->
    (L |- R b c) -> (L |- R (f a b) (f a c))

def leftReflT {L : Logic P} {R : Rel P T} {C f}
  [K : LeftReflT L R C f] {a b c} := K.leftReflT a b c

-- Right Reflection / Left Substitution
-- R a b |- R (f a c) (f b c)

-- Constrained for a given function
class RightReflT (L : Logic P) (R : Rel P T) (C : T -> P) (f : Binar T) :=
  rightReflT : (a b c : T) -> 
    (L |- C a) -> (L |- C b) -> (L |- C c) ->
    (L |- R b c) -> (L |- R (f b a) (f c a))

def rightReflT {L : Logic P} {R : Rel P T} {C f}
  [K : RightReflT L R C f] {a b c} := K.rightReflT a b c

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

instance iSymmOfComm {L : Logic P} {R : Rel P P}
  [K : Comm L R] : Symm L R := {symm := K.comm}

instance iCommOfSymm {L : Logic P} {R : Rel P P}
  [K : Symm L R] : Comm L R := {comm := K.symm}

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

--------------------------------------------------------------------------------
-- Commutativity
-- R (f a b) (f b a)
--------------------------------------------------------------------------------

-- Unconstrained

class CommOver (L : Logic P) (R : Rel P T) (f : Binar T) :=
  commOver : (a b : T) -> (L |- R (f a b) (f b a))

def commOver {L : Logic P} {R : Rel P T} {f} 
  [K : CommOver L R f] {a b} := K.commOver a b

-- Constrained

class CommOverT (L : Logic P) (R : Rel P T) (C : T -> P) (f : Binar T) :=
  commOverT : (a b : T) -> (L |- C a) -> (L |- C b) -> (L |- R (f a b) (f b a))

def commOverT {L : Logic P} {R : Rel P T} {C f}
  [K : CommOverT L R C f] {a b} := K.commOverT a b

--------------------------------------------------------------------------------
-- Associativity
--------------------------------------------------------------------------------

-- Left-to-Right
-- R (f (f a b) c) (f a (f b c))

-- Unconstrained
class LtrAssocOver (L : Logic P) (R : Rel P T) (f : Binar T) :=
  ltrAssocOver :  (a b c : T) ->  (L |- R (f (f a b) c) (f a (f b c)))

def ltrAssocOver {L : Logic P} {R : Rel P T} {f}
  [K : LtrAssocOver L R f] {a b c} := K.ltrAssocOver a b c

-- Constrained
class LtrAssocOverT (L : Logic P) (R : Rel P T) (C : T -> P) (f : Binar T) :=
  ltrAssocOverT :  (a b c : T) -> 
    (L |- C a) -> (L |- C b) -> (L |- C c) -> 
    (L |- R (f (f a b) c) (f a (f b c)))

def ltrAssocOverT {L : Logic P} [R : Rel P T] {C f}
  [K : LtrAssocOverT L R C f] {a b c} := K.ltrAssocOverT a b c

-- Right-to-Left
-- R (f a (f b c)) (f (f a b) c)

-- Unconstrained
class RtlAssocOver (L : Logic P) (R : Rel P T) (f : Binar T) :=
  rtlAssocOver :  (a b c : T) ->  (L |- R (f a (f b c)) (f (f a b) c))

def rtlAssocOver {L : Logic P} {R : Rel P T} {f}
  [K : RtlAssocOver L R f] {a b c} := K.rtlAssocOver a b c

-- Constrained
class RtlAssocOverT (L : Logic P) (R : Rel P T) (C : T -> P) (f : Binar T) :=
  rtlAssocOverT :  (a b c : T) -> 
    (L |- C a) -> (L |- C b) -> (L |- C c) -> 
    (L |- R (f a (f b c)) (f (f a b) c))

def rtlAssocOverT {L : Logic P} [R : Rel P T] {C f}
  [K : RtlAssocOverT L R C f] {a b c} := K.rtlAssocOverT a b c

end Gaea.Logic