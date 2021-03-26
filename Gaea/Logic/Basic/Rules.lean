import Gaea.Logic.Notation

universes u v

namespace Gaea.Logic

-- Forall

class ForallIntro {P : Sort u} {T : Sort v} (L : Logic P) (Fa : LForall P T) := 
  (forallIntro : (f : T -> P) -> ((a : T) -> (L |- f a)) -> (L |- lForall f))

def forallIntro {P : Sort u} {T : Sort v} {L : Logic P} [Fa : LForall P T]  
  [K : ForallIntro L Fa] {f : T -> P} := K.forallIntro f

class ForallElim {P : Sort u} {T : Sort v} (L : Logic P) (Fa : LForall P T) := 
  (forallElim : (f : T -> P) -> (L |- lForall f) -> ((a : T) -> (L |- f a)))  

def forallElim {P : Sort u} {T : Sort v} {L : Logic P} [Fa : LForall P T]  
  [K : ForallElim L Fa] {f : T -> P} := K.forallElim f

-- Exists

class ExistsIntro {P : Sort u} {T : Sort v} (L : Logic P) (X : LExists P T) := 
  (existsIntro : (f : T -> P) -> (a : T) -> (L |- f a) -> (L |- lExists f))

def existsIntro {P : Sort u} {T : Sort v} {L : Logic P} [X : LExists P T]  
  [K : ExistsIntro L X] {f : T -> P} := K.existsIntro f

class ExistsElim {P : Sort u} {T : Sort v} (L : Logic P) (X : LExists P T) := 
  (existsElim : (f : T -> P) -> (p : P) -> (L |- lExists f) -> 
    ((a : T) -> (L |- f a) -> (L |- p)) -> (L |- p))

def existsElim {P : Sort u} {T : Sort v} {L : Logic P} [X : LExists P T]  
  [K : ExistsElim L X] {f : T -> P} {p : P} := K.existsElim f p

-- If

class IfIntro {P : Sort u} (L : Logic P) (If : LIf P) := 
  (ifIntro : (p q : P) -> ((L |- p) -> (L |- q)) -> (L |- p -> q)) 

def ifIntro {P : Sort u} {L : Logic P} [If : LIf P] [K : IfIntro L If] 
  {p q : P} := K.ifIntro p q

class IfElim {P : Sort u} (L : Logic P) (If : LIf P) := 
  (ifElim : (p q : P) -> (L |- p -> q) -> ((L |- p) -> (L |- q)))

def ifElim {P : Sort u} {L : Logic P} [If : LIf P] [K : IfElim L If] 
  {p q : P} := K.ifElim p q

-- Iff

class IffIntro {P : Sort u} (L : Logic P) (Iff : LIff P) (If : LIf P) := 
  (iffIntro : (p q : P) -> (L |- p -> q) -> (L |- q -> p) -> (L |- p <-> q))

def iffIntro {P : Sort u} {L : Logic P} [Iff : LIff P] [If : LIf P]
  [K : IffIntro L Iff If] {p q : P} := K.iffIntro p q

def iffIntro' {P : Sort u} {L : Logic P} [Iff : LIff P] [If : LIf P] 
  [K : IffIntro L Iff If] [K' : IfIntro L If] {p q : P} 
  : ((L |- p) -> (L |- q)) -> ((L |- q) -> (L |- p)) -> (L |- p <-> q)
  := fun pq qp => K.iffIntro p q (K'.ifIntro p q pq) (K'.ifIntro q p qp)

class IffTo {P : Sort u} (L : Logic P) (Iff : LIff P) (If : LIf P) := 
  (iffTo : (p q : P) -> (L |- p <-> q) -> (L |- p -> q))

def iffTo {P : Sort u} {L : Logic P} [Iff : LIff P] [If : LIf P]
  [K : IffTo L Iff If] {p q : P} := K.iffTo p q

def iffTo' {P : Sort u} {L : Logic P} [Iff : LIff P] [If : LIf P] 
  [K : IffTo L Iff If] [K' : IfElim L If] {p q : P} 
  : (L |- p <-> q) -> ((L |- p) -> (L |- q))
  := fun pIff => K'.ifElim p q (K.iffTo p q pIff)

class IffFrom {P : Sort u} (L : Logic P) (Iff : LIff P) (If : LIf P) := 
  (iffFrom : (p q : P) -> (L |- p <-> q) -> (L |- q -> p))

def iffFrom {P : Sort u} {L : Logic P} [Iff : LIff P] [If : LIf P]
  [K : IffFrom L Iff If] {p q : P} := K.iffFrom p q

def iffFrom' {P : Sort u} {L : Logic P} [Iff : LIff P] [If : LIf P] 
  [K : IffFrom L Iff If] [K' : IfElim L If] {p q : P} 
  : (L |- p <-> q) -> ((L |- q) -> (L |- p))
  := fun pIff => K'.ifElim q p (K.iffFrom p q pIff)

-- Conjuction

class ConjIntro {P : Sort u} (L : Logic P) (Cj : Conj P) := 
  (conjIntro : (p q : P) -> (L |- p) -> (L |- q) -> (L |- p /\ q)) 

def conjIntro {P : Sort u} {L : Logic P} [Cj : Conj P] 
  [K : ConjIntro L Cj] {p q : P} := K.conjIntro p q

class ConjLeft {P : Sort u} (L : Logic P) (Cj : Conj P) := 
  (conjLeft : (p q : P) -> (L |- p /\ q) -> (L |- p))

def conjLeft {P : Sort u} {L : Logic P} [Cj : Conj P] 
  [K : ConjLeft L Cj] {p q : P} := K.conjLeft p q

class ConjRight {P : Sort u} (L : Logic P) (Cj : Conj P) := 
  (conjRight : (p q : P) -> (L |- p /\ q) -> (L |- q))

def conjRight {P : Sort u} {L : Logic P} [Cj : Conj P] 
  [K : ConjRight L Cj] {p q : P} := K.conjRight p q

-- Disjunction

class DisjIntroLeft {P : Sort u} (L : Logic P) (Dj : Disj P)  := 
  (disjIntroLeft : (p q : P) -> (L |- q) -> (L |- p \/ q)) 

def disjIntroLeft {P : Sort u} {L : Logic P} [Dj : Disj P] 
  [K : DisjIntroLeft L Dj] {p q : P} := K.disjIntroLeft p q

class DisjIntroRight {P : Sort u} (L : Logic P) (Dj : Disj P)  := 
  (disjIntroRight : (p q : P) -> (L |- p) -> (L |- p \/ q)) 

def disjIntroRight {P : Sort u} {L : Logic P} [Dj : Disj P] 
  [K : DisjIntroRight L Dj] {p q : P} := K.disjIntroRight p q

class DisjElim {P : Sort u} (L : Logic P) (Dj : Disj P) (If : LIf P) := 
  (disjElim : (p q r : P) -> (L |- p \/ q) -> 
    (L |- p -> r) -> (L |- q -> r) -> (L |- r))

def disjElim {P : Sort u} {L : Logic P} [Dj : Disj P] [If : LIf P] 
  [K : DisjElim L Dj If] {p q r : P} := K.disjElim p q r

def disjElim' {P : Sort u} {L : Logic P} [Dj : Disj P] [If : LIf P] 
  [K : DisjElim L Dj If] [K' : IfIntro L If] {p q r : P} 
  : (L |- p \/ q) -> ((L |- p) -> (L |- r)) -> ((L |- q) -> (L |- r)) -> (L |- r)
  := fun pq pr qr => K.disjElim p q r pq (K'.ifIntro p r pr) (K'.ifIntro q r qr)

class DisjElimLeft {P : Sort u} (L : Logic P) (Dj : Disj P) (Not : LNot P) := 
  (disjElimLeft : (p q : P) -> (L |- p \/ q) -> (L |- ~p) -> (L |- q))

def disjElimLeft {P : Sort u} {L : Logic P} [Dj : Disj P] [Not : LNot P] 
  [K : DisjElimLeft L Dj Not] {p q : P} := K.disjElimLeft p q

class DisjElimRight {P : Sort u} (L : Logic P) (Dj : Disj P) (Not : LNot P) := 
  (disjElimRight : (p q : P) -> (L |- p \/ q) -> (L |- ~q) -> (L |- p))

def disjElimRight {P : Sort u} {L : Logic P} [Dj : Disj P] [Not : LNot P] 
  [K : DisjElimRight L Dj Not] {p q : P} := K.disjElimRight p q

-- Not

class NotIntro {P : Sort u} (L : Logic P) 
  (Not : LNot P) (If : LIf P) (F : LFalse P) := 
  (notIntro : (p : P) -> (L |- p -> false) -> (L |- ~p)) 

def notIntro {P : Sort u} {L : Logic P} 
  [Not : LNot P] [If : LIf P] [F : LFalse P] 
  [K : NotIntro L Not If F] {p : P} := K.notIntro p

def notIntro' {P : Sort u} {L : Logic P} 
  [Not : LNot P] [If : LIf P] [F : LFalse P] 
  [K : NotIntro L Not If F] [K' : IfIntro L If] {p : P} 
  : ((L |- p) -> (L |- false)) -> (L |- ~p)
  := fun pf => K.notIntro p (K'.ifIntro p false pf)

class NotElim {P : Sort u} (L : Logic P) 
  (Not : LNot P) (If : LIf P) (F : LFalse P) := 
  (notElim : (p : P) -> (L |- ~p) -> ((L |- p -> false)))

def notElim {P : Sort u} {L : Logic P} 
  [Not : LNot P] [If : LIf P] [F : LFalse P] 
  [K : NotElim L Not If F] {p : P} := K.notElim p

def notElim' {P : Sort u} {L : Logic P} 
  [Not : LNot P] [If : LIf P] [F : LFalse P] 
  [K : NotElim L Not If F] [K' : IfElim L If] {p : P} 
  : (L |- ~p) -> ((L |- p) -> (L |- false)) 
  := fun np => K'.ifElim p false (K.notElim p np)

-- True

class TrueIntro {P : Sort u} (L : Logic P) (T : LTrue P) := 
  (trueIntro : L |- true) 

def trueIntro {P : Sort u} {L : Logic P} [T : LTrue P]
  [K : TrueIntro L T] := K.trueIntro

end Gaea.Logic