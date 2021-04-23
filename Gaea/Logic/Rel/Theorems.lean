import Gaea.Logic.Rel.Rules

universes u v

namespace Gaea.Logic

--------------------------------------------------------------------------------
-- Function Substitution
-- (R a b) -> (R (f a) (f b))
--------------------------------------------------------------------------------

def funSubstByReflPredSubst {P : Sort u} {T : Sort v} 
{L : Logic P} {R : Rel P T} (Rf : Refl L R) (PSb : PredSubst L R)
: (f : T -> T) -> (a b : T) -> (L |- R a b) -> (L |- R (f a) (f b))
:= by 
  intro f a b Rab
  apply predSubst (F := fun x => R (f a) (f x)) Rab 
  exact refl (f a)

instance iFunSubstByReflPredSubst {P : Sort u} {T : Sort v} 
{L : Logic P} {R : Rel P T} [Rf : Refl L R] [PSb : PredSubst L R]
: FunSubst L R := {toFun := funSubstByReflPredSubst Rf PSb}

--------------------------------------------------------------------------------
-- Symmetry
-- (R a b) -> (R b a)
--------------------------------------------------------------------------------

def symmByReflPredSubst {P : Sort u} {T : Sort v} 
{L : Logic P} {R : Rel P T} (Rf : Refl L R) (PSb : PredSubst L R)
: (a b : T) -> (L |- R a b) -> (L |- R b a)
:= by 
  intro a b Rab 
  apply predSubst (F := fun x => R x a) Rab 
  exact refl a

instance iSymmByReflPredSubst {P : Sort u} {T : Sort v} 
{L : Logic P} {R : Rel P T} [Rf : Refl L R] [PSb : PredSubst L R]
: Symm L R := {toFun := symmByReflPredSubst Rf PSb}

--------------------------------------------------------------------------------
-- Transitivity
-- (a = b) /\ (b = c) -> (a = c)
--------------------------------------------------------------------------------

def transByPredSubst {P : Sort u} {T : Sort v} 
{L : Logic P} {R : Rel P T} (PSb : PredSubst L R)
: (a b c : T) -> (L |- R a b) -> (L |- R b c) -> (L |- R a c) 
:= by 
  intro a b c Rab Rbc 
  apply predSubst (F := fun x => R a x) Rbc
  exact Rab

instance iTransByPredSubst {P : Sort u} {T : Sort v} 
{L : Logic P} {R : Rel P T} [PSb : PredSubst L R]
: Trans L R := {toFun := transByPredSubst PSb}

--------------------------------------------------------------------------------
-- Left Euclidean
-- (R b a) /\ (R c a) -> (R b c)
--------------------------------------------------------------------------------

-- Unconstrained

def leftEucBySymmTrans
{P : Sort u} {T : Sort v} 
{L : Logic P} {R : Rel P T}
(Sm : Symm L R) (Tr : Trans L R)
: (a b c : T) -> 
    (L |- R b a) -> (L |- R c a) -> (L |- R b c)
:= by
  intro a b c Rba Rca
  have Rac := symm Rca
  exact trans Rba Rac

instance iLeftEucBySymmTrans 
{P : Sort u} {T : Sort v} {L : Logic P} {R : Rel P T} 
[Sm : Symm L R] [Tr : Trans L R] : LeftEuc L R := 
{toFun := leftEucBySymmTrans Sm Tr}

-- Constrained

def leftEucBySymmTransT 
{P : Sort u} {T : Sort v} {L : Logic P} {R : Rel P T} {C : T -> P} 
(Sm : SymmT L R C) (Tr : TransT L R C)
: (a b c : T) -> 
    (L |- C a) -> (L |- C b) -> (L |- C c) -> 
    (L |- R b a) -> (L |- R c a) -> (L |- R b c)
:= by
  intro a b c Ca Cb Cc Rba Rca
  have Rac := symmT Cc Ca Rca
  exact transT Cb Ca Cc Rba Rac

instance iLeftEucBySymmTransT 
{P : Sort u} {T : Sort v} {L : Logic P} {R : Rel P T} {C : T -> P}  
[Sm : SymmT L R C] [Tr : TransT L R C] : LeftEucT L R C := 
{toFun := leftEucBySymmTransT Sm Tr}

--------------------------------------------------------------------------------
-- Right Euclidean
-- (b = a) /\ (c = a) -> (b = c)
--------------------------------------------------------------------------------

-- Unconstrained

def rightEucBySymmTrans
{P : Sort u} {T : Sort v} 
{L : Logic P} {R : Rel P T}
(Sm : Symm L R) (Tr : Trans L R)
: (a b c : T) -> 
    (L |- R a b) -> (L |- R a c) -> (L |- R b c)
:= by
  intro a b c Rab Rac
  have Rba := symm Rab
  exact trans Rba Rac

instance iRightEucBySymmTrans
{P : Sort u} {T : Sort v} {L : Logic P} {R : Rel P T} 
[Sm : Symm L R] [Tr : Trans L R] : RightEuc L R := 
{toFun := rightEucBySymmTrans Sm Tr}

-- Constrained

def rightEucBySymmTransT
{P : Sort u} {T : Sort v} {L : Logic P} {R : Rel P T} {C : T -> P} 
(Sm : SymmT L R C) (Tr : TransT L R C)
: (a b c : T) -> 
    (L |- C a) -> (L |- C b) -> (L |- C c) -> 
    (L |- R a b) -> (L |- R a c) -> (L |- R b c)
:= by
  intro a b c Ca Cb Cc Rab Rac
  have Rba := symmT Ca Cb Rab
  exact transT Cb Ca Cc Rba Rac

instance iRightEucBySymmTransT 
{P : Sort u} {T : Sort v} {L : Logic P} {R : Rel P T} {C : T -> P}  
[Sm : SymmT L R C] [Tr : TransT L R C] : RightEucT L R C := 
{toFun := rightEucBySymmTransT Sm Tr}

--------------------------------------------------------------------------------
-- Join
-- (x = a) /\ (y = b) /\ (a = b) -> (x = y)
--------------------------------------------------------------------------------

-- By Trans/LeftEuc

def relJoinByTransLeftEucT
{P : Sort u} {T : Sort v} {L : Logic P} {R : Rel P T} {C : T -> P}
(Tr : TransT L R C) (LEu : LeftEucT L R C)
: (a b c d : T) -> 
  (L |- C a) -> (L |- C b) -> (L |- C c) -> (L |- C d) ->
  (L |- R a c) -> (L |- R b d) -> (L |- R c d) -> (L |- R a b)
:= by
  intro a b c d Ca Cb Cc Cd Rac Rbd Rcd
  exact leftEucT Cd Ca Cb (transT Ca Cc Cd Rac Rcd) Rbd

instance iRelJoinByTransLeftEucT
{P : Sort u} {T : Sort v} {L : Logic P} {R : Rel P T} {C : T -> P} 
[Tr : TransT L R C] [LEu : LeftEucT L R C] : RelJoinT L R C := 
{toFun := relJoinByTransLeftEucT Tr LEu}

-- By Symm/Trans

def relJoinBySymmTransT
{P : Sort u} {T : Sort v} {L : Logic P} {R : Rel P T} {C : T -> P} 
(Sm : SymmT L R C) (Tr : TransT L R C)
: (a b c d : T) -> 
  (L |- C a) -> (L |- C b) -> (L |- C c) -> (L |- C d) ->
  (L |- R a c) -> (L |- R b d) -> (L |- R c d) -> (L |- R a b)
:= by
  intro a b c d Ca Cb Cc Cd Rac Rbd Rcd
  exact transT Ca Cd Cb (transT Ca Cc Cd Rac Rcd) (symmT Cb Cd Rbd)

instance iRelJoinBySymmTransT 
{P : Sort u} {T : Sort v} {L : Logic P} {R : Rel P T} {C : T -> P} 
[Sm : SymmT L R C] [Tr : TransT L R C] : RelJoinT L R C 
:= {toFun := relJoinBySymmTransT Sm Tr}

end Gaea.Logic