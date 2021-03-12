import Gaea.Logic
import Gaea.Syntax.Logic
import Gaea.Logic.Notation
import Gaea.Syntax.Notation

universes u v

open Gaea.Syntax

namespace Gaea.Logic.Rules

-- Forall

def ForallIntro {P : Sort u} (L : Logic P) (T : Sort v) [LForall P T] := 
  (f : T -> P) -> ((a : T) -> (L |- f a)) -> (L |- lForall f) 

def ForallElim {P : Sort u} (L : Logic P) (T : Sort v) [LForall P T] := 
  (f : T -> P) -> (L |- lForall f) -> ((a : T) -> (L |- f a))  

-- If

def IfIntro {P : Sort u} (L : Logic P) [LIf P] := 
  (p q : P) -> ((L |- p) -> (L |- q)) -> (L |- p -> q) 

def IfElim {P : Sort u} (L : Logic P) [LIf P] := 
  (p q : P) -> (L |- p -> q) -> ((L |- p) -> (L |- q))  

-- Equality

def EqRefl {P : Sort u} {T : Sort v} (L : Logic P) (C : LEq P T) :=
  (x : T) -> L |- x = x

def EqSymm {P : Sort u} {T : Sort v} (L : Logic P) (C : LEq P T) :=
  (x y : T) -> (L |- x = y) -> (L |- y = x)

def EqTrans {P : Sort u} {T : Sort v} (L : Logic P)  (C : LEq P T) :=
  (x y z : T) -> (L |- x = y) -> (L |- y = z) -> (L |- x = z)

end Gaea.Logic.Rules