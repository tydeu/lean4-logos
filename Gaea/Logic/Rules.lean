import Gaea.Logic
import Gaea.Syntax.Logic
import Gaea.Logic.Notation
import Gaea.Syntax.Notation

universes u v

open Gaea.Syntax

namespace Gaea.Logic.Rules

-- Forall

def ForallIntro {P : Sort u} {T : Sort v} (L : Logic P) (Fa : LForall P T) := 
  (f : T -> P) -> ((a : T) -> (L |- f a)) -> (L |- lForall f) 

def ForallElim {P : Sort u} {T : Sort v} (L : Logic P) (Fa : LForall P T) := 
  (f : T -> P) -> (L |- lForall f) -> ((a : T) -> (L |- f a))  

-- Exists

def ExistsIntro {P : Sort u} {T : Sort v} (L : Logic P) (X : LExists P T) := 
  (f : T -> P) -> (a : T) -> (L |- f a) -> (L |- lExists f) 

def ExistsElim {P : Sort u} {T : Sort v} (L : Logic P) (X : LExists P T) := 
  (f : T -> P) -> (p : P) -> (L |- lExists f) -> 
    ((a : T) -> (L |- f a) -> (L |- p)) -> (L |- p)

-- If

def IfIntro {P : Sort u} (L : Logic P) (If : LIf P) := 
  (p q : P) -> ((L |- p) -> (L |- q)) -> (L |- p -> q) 

def IfElim {P : Sort u} (L : Logic P) (If : LIf P) := 
  (p q : P) -> (L |- p -> q) -> ((L |- p) -> (L |- q))  

-- Iff

def IfFIntro {P : Sort u} (L : Logic P) (Iff : LIff P) (If : LIf P) := 
  (p q : P) -> (L |- p -> q) -> (L |- p -> q) -> (L |- p <-> q) 

def IffTo {P : Sort u} (L : Logic P) (Iff : LIff P) (If : LIf P) := 
  (p q : P) -> (L |- p <-> q) -> (L |- p -> q)  

def IffFrom {P : Sort u} (L : Logic P) (Iff : LIff P) (If : LIf P) := 
  (p q : P) -> (L |- p <-> q) -> (L |- q -> p)  

-- And

def AndIntro {P : Sort u} (L : Logic P) (And : LAnd P) := 
  (p q : P) -> (L |- p) -> (L |- q) -> (L |- p /\ q) 

def AndLeft {P : Sort u} (L : Logic P) (And : LAnd P) := 
  (p q : P) -> (L |- p /\ q) -> (L |- p)  

def AndRight {P : Sort u} (L : Logic P) (And : LAnd P) := 
  (p q : P) -> (L |- p /\ q) -> (L |- q)  

-- Equality

def EqRefl {P : Sort u} {T : Sort v} (L : Logic P) (Eq : LEq P T) :=
  (x : T) -> L |- x = x

def EqSymm {P : Sort u} {T : Sort v} (L : Logic P) (Eq : LEq P T) :=
  (x y : T) -> (L |- x = y) -> (L |- y = x)

def EqTrans {P : Sort u} {T : Sort v} (L : Logic P) (Eq : LEq P T) :=
  (x y z : T) -> (L |- x = y) -> (L |- y = z) -> (L |- x = z)

end Gaea.Logic.Rules