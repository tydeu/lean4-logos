import Gaea.Logic.Rel.Rules

universes u v

namespace Gaea.Logic

--------------------------------------------------------------------------------
-- Function Substitution
-- (R a b) -> (R (f a) (f b))
--------------------------------------------------------------------------------

def funSubstByReflPredSubst {P : Sort u} {T : Sort v} 
{L : Logic P} {R : T -> T -> P} (Rf : Refl L R) (PSb : PredSubst L R)
: (a b : T) -> (f : T -> T) -> (L |- R a b) -> (L |- R (f a) (f b))
:= by 
  intro a b f Rab
  apply predSubst (fun x => R (f a) (f x)) Rab 
  exact refl (f a)

instance iFunSubstByReflPredSubst {P : Sort u} {T : Sort v} 
{L : Logic P} {R : T -> T -> P} [Rf : Refl L R] [PSb : PredSubst L R]
: FunSubst L R := {funSubst := funSubstByReflPredSubst Rf PSb}

--------------------------------------------------------------------------------
-- Symmetry
-- (R a b) -> (R b a)
--------------------------------------------------------------------------------

def symmByReflPredSubst {P : Sort u} {T : Sort v} 
{L : Logic P} {R : T -> T -> P} (Rf : Refl L R) (PSb : PredSubst L R)
: (a b : T) -> (L |- R a b) -> (L |- R b a)
:= by 
  intro a b Rab 
  apply predSubst (fun x => R x a) Rab 
  exact refl a

instance iSymmByReflPredSubst {P : Sort u} {T : Sort v} 
{L : Logic P} {R : T -> T -> P} [Rf : Refl L R] [PSb : PredSubst L R]
: Symm L R := {symm := symmByReflPredSubst Rf PSb}

--------------------------------------------------------------------------------
-- Transitivity
-- (a = b) /\ (b = c) -> (a = c)
--------------------------------------------------------------------------------

def transByPredSubst {P : Sort u} {T : Sort v} 
{L : Logic P} {R : T -> T -> P} (PSb : PredSubst L R)
: (a b c : T) -> (L |- R a b) -> (L |- R b c) -> (L |- R a c) 
:= by 
  intro a b c Rab Rbc 
  apply predSubst (fun x => R a x) Rbc
  exact Rab

instance iTransByPredSubst {P : Sort u} {T : Sort v} 
{L : Logic P} {R : T -> T -> P} [PSb : PredSubst L R]
: Trans L R := {trans := transByPredSubst PSb}

--------------------------------------------------------------------------------
-- Left Euclidean
-- (R b a) /\ (R c a) -> (R b c)
--------------------------------------------------------------------------------

-- Unconstrained

def leftEucBySymmTrans
{P : Sort u} {T : Sort v} 
{L : Logic P} {R : T -> T -> P}
(Sm : Symm L R) (Tr : Trans L R)
: (a b c : T) -> 
    (L |- R b a) -> (L |- R c a) -> (L |- R b c)
:= by
  intro a b c Rba Rca
  have Rac := symm Rca
  exact trans Rba Rac

instance iLeftEucBySymmTrans 
{P : Sort u} {T : Sort v} {L : Logic P} {R : T -> T -> P} 
[Sm : Symm L R] [Tr : Trans L R] : LeftEuc L R := 
{leftEuc := leftEucBySymmTrans Sm Tr}

-- Constrained

def memLeftEucBySymmTrans 
{P : Sort u} {T : Sort v} {L : Logic P} {R : T -> T -> P} {C : T -> P} 
(Sm : MemSymm L R C) (Tr : MemTrans L R C)
: (a b c : T) -> 
    (L |- C a) -> (L |- C b) -> (L |- C c) -> 
    (L |- R b a) -> (L |- R c a) -> (L |- R b c)
:= by
  intro a b c Ca Cb Cc Rba Rca
  have Rac := memSymm Cc Ca Rca
  exact memTrans Cb Ca Cc Rba Rac

instance iMemLeftEucBySymmTrans 
{P : Sort u} {T : Sort v} {L : Logic P} {R : T -> T -> P} {C : T -> P}  
[Sm : MemSymm L R C] [Tr : MemTrans L R C] : MemLeftEuc L R C := 
{memLeftEuc := memLeftEucBySymmTrans Sm Tr}

--------------------------------------------------------------------------------
-- Right Euclidean
-- (b = a) /\ (c = a) -> (b = c)
--------------------------------------------------------------------------------

-- Unconstrained

def rightEucBySymmTrans
{P : Sort u} {T : Sort v} 
{L : Logic P} {R : T -> T -> P}
(Sm : Symm L R) (Tr : Trans L R)
: (a b c : T) -> 
    (L |- R a b) -> (L |- R a c) -> (L |- R b c)
:= by
  intro a b c Rab Rac
  have Rba := symm Rab
  exact trans Rba Rac

instance iRightEucBySymmTrans
{P : Sort u} {T : Sort v} {L : Logic P} {R : T -> T -> P} 
[Sm : Symm L R] [Tr : Trans L R] : RightEuc L R := 
{rightEuc := rightEucBySymmTrans Sm Tr}

-- Constrained

def memRightEucBySymmTrans
{P : Sort u} {T : Sort v} {L : Logic P} {R : T -> T -> P} {C : T -> P} 
(Sm : MemSymm L R C) (Tr : MemTrans L R C)
: (a b c : T) -> 
    (L |- C a) -> (L |- C b) -> (L |- C c) -> 
    (L |- R a b) -> (L |- R a c) -> (L |- R b c)
:= by
  intro a b c Ca Cb Cc Rab Rac
  have Rba := memSymm Ca Cb Rab
  exact memTrans Cb Ca Cc Rba Rac

instance iMemRightEucBySymmTrans 
{P : Sort u} {T : Sort v} {L : Logic P} {R : T -> T -> P} {C : T -> P}  
[Sm : MemSymm L R C] [Tr : MemTrans L R C] : MemRightEuc L R C := 
{memRightEuc := memRightEucBySymmTrans Sm Tr}

--------------------------------------------------------------------------------
-- Join
-- (x = a) /\ (y = b) /\ (a = b) -> (x = y)
--------------------------------------------------------------------------------

-- By Trans/LeftEuc

def relMemJoinByTransLeftEuc
{P : Sort u} {T : Sort v} {L : Logic P} {R : T -> T -> P} {C : T -> P}
(Tr : MemTrans L R C) (LEu : MemLeftEuc L R C)
: (x y a b : T) -> 
  (L |- C x) -> (L |- C y) -> (L |- C a) -> (L |- C b) ->
  (L |- R x a) -> (L |- R y b) -> (L |- R a b) -> (L |- R x y)
:= by
  intro x y a b Cx Cy Ca Cb Rxa Ryb Rab
  exact memLeftEuc Cb Cx Cy (memTrans Cx Ca Cb Rxa Rab) Ryb

instance iRelMemJoinByTransLeftEuc
{P : Sort u} {T : Sort v} {L : Logic P} {R : T -> T -> P} {C : T -> P} 
[Tr : MemTrans L R C] [LEu : MemLeftEuc L R C] : RelMemJoin L R C := 
{relMemJoin := relMemJoinByTransLeftEuc Tr LEu}

-- By Symm/Trans

def relMemJoinBySymmTrans
{P : Sort u} {T : Sort v} {L : Logic P} {R : T -> T -> P} {C : T -> P} 
(Sm : MemSymm L R C) (Tr : MemTrans L R C)
: (x y a b : T) -> 
  (L |- C x) -> (L |- C y) -> (L |- C a) -> (L |- C b) ->
  (L |- R x a) -> (L |- R y b) -> (L |- R a b) -> (L |- R x y)
:= by
  intro x y a b Cx Cy Ca Cb Rxa Ryb Rab
  exact memTrans Cx Cb Cy (memTrans Cx Ca Cb Rxa Rab) (memSymm Cy Cb Ryb)

instance iRelMemJoinBySymmTrans 
{P : Sort u} {T : Sort v} {L : Logic P} {R : T -> T -> P} {C : T -> P} 
[Sm : MemSymm L R C] [Tr : MemTrans L R C] : RelMemJoin L R C 
:= {relMemJoin := relMemJoinBySymmTrans Sm Tr}

end Gaea.Logic