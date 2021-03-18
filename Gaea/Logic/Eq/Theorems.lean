import Gaea.Logic.Eq.Rules
import Gaea.Logic.Rel.Theorems

universes u v

namespace Gaea.Logic

def eqFunSubst_proof {P : Sort u} {T : Sort v} 
{L : Logic P} [Q : LEq P T] [EqRefl L Q] [EqPredSubst L Q]
: (a b : T) -> (f : T -> T) -> (L |- a = b) -> (L |- f a = f b)
:= by
  intro a b f Qab
  apply eqPredSubst' 
    fun x => Q.lEq (f a) (f x) 
  exact Qab 
  exact eqRefl (f a)

instance eqFunSubst_inst {P : Sort u} {T : Sort v} 
{L : Logic P} [Q : LEq P T] [EqRefl L Q] [EqPredSubst L Q]
: EqFunSubst L Q := {eqFunSubst := eqFunSubst_proof}

def eqSymm_proof {P : Sort u} {T : Sort v} 
{L : Logic P} [Q : LEq P T] [EqRefl L Q] [EqPredSubst L Q]
: (a b : T) -> (L |- a = b) -> (L |- b = a)
:= by
  intro a b Qab
  apply eqPredSubst' 
    fun x => Q.lEq x a 
  exact Qab 
  exact eqRefl a

instance eqSymm_inst {P : Sort u} {T : Sort v} 
{L : Logic P} [Q : LEq P T] [EqRefl L Q] [EqPredSubst L Q]
: EqSymm L Q := {eqSymm := eqSymm_proof}

def eqTrans_proof {P : Sort u} {T : Sort v} 
{L : Logic P} [Q : LEq P T] [EqPredSubst L Q]
: (a b c : T) -> (L |- a = b) -> (L |- b = c) -> (L |- a = c) 
:= by
  intro a b c Qab Qbc
  apply eqPredSubst' 
    fun x => Q.lEq a x 
  exact Qbc 
  exact Qab

instance eqTrans_inst {P : Sort u} {T : Sort v} 
{L : Logic P} [Q : LEq P T] [EqRefl L Q] [EqPredSubst L Q]
: EqTrans L Q := {eqTrans := eqTrans_proof}

end Gaea.Logic