import Gaea.Logic.Notation

universes u v

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

class IffIntro {P : Sort u} (L : Logic P) (Iff : LIff P) (If : LIf P) := 
  (iffIntro : (p q : P) -> (L |- p -> q) -> (L |- q -> p) -> (L |- p <-> q))

def iffIntro {P : Sort u} {L : Logic P} [Iff : LIff P] [If : LIf P]
  [C : IffIntro L Iff If] {p q : P} := C.iffIntro p q

def iffIntro' {P : Sort u} {L : Logic P} [Iff : LIff P] [If : LIf P] 
  [C : IffIntro L Iff If] [C' : IfIntro L If] {p q : P} 
  : ((L |- p) -> (L |- q)) -> ((L |- q) -> (L |- p)) -> (L |- p <-> q)
  := fun pq qp => C.iffIntro p q (C'.ifIntro p q pq) (C'.ifIntro q p qp)

class IffTo {P : Sort u} (L : Logic P) (Iff : LIff P) (If : LIf P) := 
  (iffTo : (p q : P) -> (L |- p <-> q) -> (L |- p -> q))

def iffTo {P : Sort u} {L : Logic P} [Iff : LIff P] [If : LIf P]
  [C : IffTo L Iff If] {p q : P} := C.iffTo p q

def iffTo' {P : Sort u} {L : Logic P} [Iff : LIff P] [If : LIf P] 
  [C : IffTo L Iff If] [C' : IfElim L If] {p q : P} 
  : (L |- p <-> q) -> ((L |- p) -> (L |- q))
  := fun pIff => C'.ifElim p q (C.iffTo p q pIff)

class IffFrom {P : Sort u} (L : Logic P) (Iff : LIff P) (If : LIf P) := 
  (iffFrom : (p q : P) -> (L |- p <-> q) -> (L |- q -> p))

def iffFrom {P : Sort u} {L : Logic P} [Iff : LIff P] [If : LIf P]
  [C : IffFrom L Iff If] {p q : P} := C.iffFrom p q

def iffFrom' {P : Sort u} {L : Logic P} [Iff : LIff P] [If : LIf P] 
  [C : IffFrom L Iff If] [C' : IfElim L If] {p q : P} 
  : (L |- p <-> q) -> ((L |- q) -> (L |- p))
  := fun pIff => C'.ifElim q p (C.iffFrom p q pIff)

-- And

class AndIntro {P : Sort u} (L : Logic P) (And : LAnd P) := 
  (andIntro : (p q : P) -> (L |- p) -> (L |- q) -> (L |- p /\ q)) 

def andIntro {P : Sort u} {L : Logic P} [And : LAnd P] 
  [C : AndIntro L And] {p q : P} := C.andIntro p q

class AndLeft {P : Sort u} (L : Logic P) (And : LAnd P) := 
  (andLeft : (p q : P) -> (L |- p /\ q) -> (L |- p))

def andLeft {P : Sort u} {L : Logic P} [And : LAnd P] 
  [C : AndLeft L And] {p q : P} := C.andLeft p q

class AndRight {P : Sort u} (L : Logic P) (And : LAnd P) := 
  (andRight : (p q : P) -> (L |- p /\ q) -> (L |- q))

def andRight {P : Sort u} {L : Logic P} [And : LAnd P] 
  [C : AndRight L And] {p q : P} := C.andRight p q

-- Not

class NotIntro {P : Sort u} (L : Logic P) 
  (Not : LNot P) (If : LIf P) (F : LFalse P) := 
  (notIntro : (p : P) -> (L |- p -> false) -> (L |- ~p)) 

def notIntro {P : Sort u} {L : Logic P} 
  [Not : LNot P] [If : LIf P] [F : LFalse P] 
  [C : NotIntro L Not If F] {p : P} := C.notIntro p

def notIntro' {P : Sort u} {L : Logic P} 
  [Not : LNot P] [If : LIf P] [F : LFalse P] 
  [C : NotIntro L Not If F] [C' : IfIntro L If] {p : P} 
  : ((L |- p) -> (L |- false)) -> (L |- ~p)
  := fun pf => C.notIntro p (C'.ifIntro p false pf)

class NotElim {P : Sort u} (L : Logic P) 
  (Not : LNot P) (If : LIf P) (F : LFalse P) := 
  (notElim : (p : P) -> (L |- ~p) -> ((L |- p -> false)))

def notElim {P : Sort u} {L : Logic P} 
  [Not : LNot P] [If : LIf P] [F : LFalse P] 
  [C : NotElim L Not If F] {p : P} := C.notElim p

def notElim' {P : Sort u} {L : Logic P} 
  [Not : LNot P] [If : LIf P] [F : LFalse P] 
  [C : NotElim L Not If F] [C' : IfElim L If] {p : P} 
  : (L |- ~p) -> ((L |- p) -> (L |- false)) 
  := fun np => C'.ifElim p false (C.notElim p np)

-- True

class TrueIntro {P : Sort u} (L : Logic P) (T : LTrue P) := 
  (trueIntro : L |- true) 

def trueIntro {P : Sort u} {L : Logic P} [T : LTrue P]
  [C : TrueIntro L T] := C.trueIntro

end Gaea.Logic