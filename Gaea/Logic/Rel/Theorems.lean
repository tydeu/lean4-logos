import Gaea.Logic.Rel.Rules

universes u v

open Gaea.Syntax (LEq)

namespace Gaea.Logic

-- (b = a) /\ (c = a) -> (b = c)

def leftEuc_proof 
{P : Sort u} {T : Type v} 
{L : Logic P} {R : T -> T -> P}
[Symm L R] [Trans L R]
: (a b c : T) -> 
    (L |- R b a) -> (L |- R c a) -> (L |- R b c)
:= by
  intro a b c Rba Rca
  have Rac := symm Rca
  exact trans Rba Rac

instance leftEuc_inst {P : Sort u} {T : Type v} 
{L : Logic P} {R : T -> T -> P} [Symm L R] [Trans L R]
: LeftEuc L R := {leftEuc := leftEuc_proof}

def memLeftEuc_proof 
{P : Sort u} {T : Type v} 
{L : Logic P} {R : T -> T -> P} {C : T -> P} 
[MemSymm L R C] [MemTrans L R C]
: (a b c : T) -> 
    (L |- C a) -> (L |- C b) -> (L |- C c) -> 
    (L |- R b a) -> (L |- R c a) -> (L |- R b c)
:= by
  intro a b c Ca Cb Cc Rba Rca
  have Rac := memSymm Cc Ca Rca
  exact memTrans Cb Ca Cc Rba Rac

instance memLeftEuc_inst {P : Sort u} {T : Type v} 
{L : Logic P} {R : T -> T -> P} {C : T -> P} [MemSymm L R C] [MemTrans L R C]
: MemLeftEuc L R C := {memLeftEuc := memLeftEuc_proof}

-- (b = a) /\ (c = a) -> (b = c)

def rightEuc_proof
{P : Sort u} {T : Type v} 
{L : Logic P} {R : T -> T -> P}
[Symm L R] [Trans L R]
: (a b c : T) -> 
    (L |- R a b) -> (L |- R a c) -> (L |- R b c)
:= by
  intro a b c Rab Rac
  have Rba := symm Rab
  exact trans Rba Rac

instance RightEuc_inst {P : Sort u} {T : Type v} 
{L : Logic P} {R : T -> T -> P} [Symm L R] [Trans L R]
: RightEuc L R := {rightEuc := rightEuc_proof}

def memRightEuc_proof
{P : Sort u} {T : Type v} 
{L : Logic P} {R : T -> T -> P} {C : T -> P}
[MemSymm L R C] [MemTrans L R C]
: (a b c : T) -> 
    (L |- C a) -> (L |- C b) -> (L |- C c) -> 
    (L |- R a b) -> (L |- R a c) -> (L |- R b c)
:= by
  intro a b c Ca Cb Cc Rab Rac
  have Rba := memSymm Ca Cb Rab
  exact memTrans Cb Ca Cc Rba Rac

instance memRightEuc_inst {P : Sort u} {T : Type v} 
{L : Logic P} {R : T -> T -> P} {C : T -> P}  [MemSymm L R C] [MemTrans L R C]
: MemRightEuc L R C := {memRightEuc := memRightEuc_proof}

end Gaea.Logic