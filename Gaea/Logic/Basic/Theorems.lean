import Gaea.Logic.Basic.Rules
import Gaea.Logic.Classic.Rules

namespace Gaea.Logic

universe u
variable {P : Sort u}

--------------------------------------------------------------------------------
-- Contrapositive
--------------------------------------------------------------------------------

-- (~q |- ~p) |- (p -> q)

def contraIfIntroByIfNotDne {L : Logic P} 
{If : LIf P} {Nt : LNot P} {F : LFalse P}
(IfI : IfIntro L If) 
(NtI : NotIntro L Nt F)
(NtE : NotElim L Nt F)
(DnE : DblNegElim L Nt)
: (p q : P) -> ((L |- ~q) -> (L |- ~p)) -> (L |- p -> q)
:= by
  intro p q Nq_to_Np
  apply ifIntro; intro Lp
  apply dblNegElim
  apply notIntro; intro LNq
  have LNp := Nq_to_Np LNq
  exact notElim LNp Lp

instance iContraIfIntroByIfNotDne {L : Logic P} 
[If : LIf P] [Nt : LNot P] [F : LFalse P]
[IfI : IfIntro L If]
[NtI : NotIntro L Nt F]
[NtE : NotElim L Nt F]
[DnE : DblNegElim L Nt]
: ContraIfIntro L If Nt :=
{contraIfIntro := contraIfIntroByIfNotDne IfI NtI NtE DnE}

-- (p -> q) |- (~q |- ~p) 

def contraIfElimByIfNot {L : Logic P} 
{If : LIf P} {Nt : LNot P} {F : LFalse P}
(IfE : IfElim L If) 
(NtI : NotIntro L Nt F)
(NtE : NotElim L Nt F)
: (p q : P) -> (L |- p -> q) -> (L |- ~q) -> (L |- ~p)
:= by
  intro p q LpTq LNq
  apply notIntro; intro Lp
  have Lq := ifElim LpTq Lp
  exact notElim LNq Lq

instance iContraIfElimByIfNot {L : Logic P} 
[If : LIf P] [Nt : LNot P] [F : LFalse P]
[IfE : IfElim L If]
[NtI : NotIntro L Nt F]
[NtE : NotElim L Nt F]
: ContraIfElim L If Nt :=
{contraIfElim := contraIfElimByIfNot IfE NtI NtE}

end Gaea.Logic