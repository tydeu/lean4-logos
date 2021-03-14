import Gaea.Logic.Basic
import Gaea.Syntax.Logic
import Gaea.Logic.Notation
import Gaea.Syntax.Notation

universes u v

open Gaea.Syntax

namespace Gaea.Logic

-- Forall

class ForallIntro {P : Sort u} {T : Sort v} (L : Logic P) (Fa : LForall P T) := 
  (forallIntro : (f : T -> P) -> ((a : T) -> (L |- f a)) -> (L |- lForall f))

def forallIntro {P : Sort u} {T : Sort v} {L : Logic P} [Fa : LForall P T]  
  [C : ForallIntro L Fa] {f : T -> P} := C.forallIntro f

class ForallElim {P : Sort u} {T : Sort v} (L : Logic P) (Fa : LForall P T) := 
  (forallElim : (f : T -> P) -> (L |- lForall f) -> ((a : T) -> (L |- f a)))  

def forallElim {P : Sort u} {T : Sort v} {L : Logic P} [Fa : LForall P T]  
  [C : ForallElim L Fa] {f : T -> P} := C.forallElim f

-- Exists

class ExistsIntro {P : Sort u} {T : Sort v} (L : Logic P) (X : LExists P T) := 
  (existsIntro : (f : T -> P) -> (a : T) -> (L |- f a) -> (L |- lExists f))

def existsIntro {P : Sort u} {T : Sort v} {L : Logic P} [X : LExists P T]  
  [C : ExistsIntro L X] {f : T -> P} := C.existsIntro f

class ExistsElim {P : Sort u} {T : Sort v} (L : Logic P) (X : LExists P T) := 
  (existsElim : (f : T -> P) -> (p : P) -> (L |- lExists f) -> 
    ((a : T) -> (L |- f a) -> (L |- p)) -> (L |- p))

def existsElim {P : Sort u} {T : Sort v} {L : Logic P} [X : LExists P T]  
  [C : ExistsElim L X] {f : T -> P} {p : P} := C.existsElim f p

-- If

class IfIntro {P : Sort u} (L : Logic P) (If : LIf P) := 
  (ifIntro : (p q : P) -> ((L |- p) -> (L |- q)) -> (L |- p -> q)) 

def ifIntro {P : Sort u} {L : Logic P} [If : LIf P] [C : IfIntro L If] 
  {p q : P} := C.ifIntro p q

class IfElim {P : Sort u} (L : Logic P) (If : LIf P) := 
  (ifElim : (p q : P) -> (L |- p -> q) -> ((L |- p) -> (L |- q)))

def ifElim {P : Sort u} {L : Logic P} [If : LIf P] [C : IfElim L If] 
  {p q : P} := C.ifElim p q

-- Iff

class IfFIntro {P : Sort u} (L : Logic P) (Iff : LIff P) (If : LIf P) := 
  (iffIntro : (p q : P) -> (L |- p -> q) -> (L |- p -> q) -> (L |- p <-> q))

export IfFIntro (iffIntro)

class IffTo {P : Sort u} (L : Logic P) (Iff : LIff P) (If : LIf P) := 
  (iffTo : (p q : P) -> (L |- p <-> q) -> (L |- p -> q))

export IffTo (iffTo)

class IffFrom {P : Sort u} (L : Logic P) (Iff : LIff P) (If : LIf P) := 
  (iffFrom : (p q : P) -> (L |- p <-> q) -> (L |- q -> p))

export IffFrom (iffFrom)

-- And

class AndIntro {P : Sort u} (L : Logic P) (And : LAnd P) := 
  (andIntro : (p q : P) -> (L |- p) -> (L |- q) -> (L |- p /\ q)) 

export AndIntro (andIntro)

class AndLeft {P : Sort u} (L : Logic P) (And : LAnd P) := 
  (andLeft : (p q : P) -> (L |- p /\ q) -> (L |- p))

export AndLeft (andLeft)

class AndRight {P : Sort u} (L : Logic P) (And : LAnd P) := 
  (andRight : (p q : P) -> (L |- p /\ q) -> (L |- q))

export AndRight (andRight)

end Gaea.Logic