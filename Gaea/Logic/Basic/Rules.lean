import Gaea.Logic.Notation

universes u v

namespace Gaea.Logic

--------------------------------------------------------------------------------
-- Forall
--------------------------------------------------------------------------------

class ForallIntro {P : Sort u} {T : Sort v} (L : Logic P) (Fa : LForall P T) := 
  forallIntro : (f : T -> P) -> ((a : T) -> (L |- f a)) -> (L |- lForall f)

def forallIntro {P : Sort u} {T : Sort v} {L : Logic P} [Fa : LForall P T]  
  [K : ForallIntro L Fa] {f : T -> P} := K.forallIntro f

class ForallElim {P : Sort u} {T : Sort v} (L : Logic P) (Fa : LForall P T) := 
  forallElim : (f : T -> P) -> (L |- lForall f) -> ((a : T) -> (L |- f a))  

def forallElim {P : Sort u} {T : Sort v} {L : Logic P} [Fa : LForall P T]  
  [K : ForallElim L Fa] {f : T -> P} := K.forallElim f

--------------------------------------------------------------------------------
-- Exists
--------------------------------------------------------------------------------

class ExistsIntro {P : Sort u} {T : Sort v} (L : Logic P) (X : LExists P T) := 
  existsIntro : (f : T -> P) -> (a : T) -> (L |- f a) -> (L |- lExists f)

def existsIntro {P : Sort u} {T : Sort v} {L : Logic P} [X : LExists P T]  
  [K : ExistsIntro L X] {f : T -> P} := K.existsIntro f

class ExistsElim {P : Sort u} {T : Sort v} (L : Logic P) (X : LExists P T) := 
  existsElim : (f : T -> P) -> (p : P) -> (L |- lExists f) -> 
    ((a : T) -> (L |- f a) -> (L |- p)) -> (L |- p)

def existsElim {P : Sort u} {T : Sort v} {L : Logic P} [X : LExists P T]  
  [K : ExistsElim L X] {f : T -> P} {p : P} := K.existsElim f p

--------------------------------------------------------------------------------
-- If
--------------------------------------------------------------------------------

-- (L |- p -> q) <-> (p -> q) 

class IfIntro {P : Sort u} (L : Logic P) (If : LIf P) := 
  ifIntro : (p q : P) -> ((L |- p) -> (L |- q)) -> (L |- p -> q) 

def ifIntro {P : Sort u} {L : Logic P} [If : LIf P] [K : IfIntro L If] 
  {p q : P} := K.ifIntro p q

class IfElim {P : Sort u} (L : Logic P) (If : LIf P) := 
  ifElim : (p q : P) -> (L |- p -> q) -> ((L |- p) -> (L |- q))

def ifElim {P : Sort u} {L : Logic P} [If : LIf P] [K : IfElim L If] 
  {p q : P} := K.ifElim p q

--------------------------------------------------------------------------------
-- Iff
--------------------------------------------------------------------------------

class IffIntro {P : Sort u} (L : Logic P) (Iff : LIff P) (If : LIf P) := 
  iffIntro : (p q : P) -> (L |- p -> q) -> (L |- q -> p) -> (L |- p <-> q)

def iffIntro {P : Sort u} {L : Logic P} [Iff : LIff P] [If : LIf P]
  [K : IffIntro L Iff If] {p q : P} := K.iffIntro p q

def iffIntro' {P : Sort u} {L : Logic P} [Iff : LIff P] [If : LIf P] 
  [K : IffIntro L Iff If] [K' : IfIntro L If] {p q : P} 
  : ((L |- p) -> (L |- q)) -> ((L |- q) -> (L |- p)) -> (L |- p <-> q)
  := fun pq qp => K.iffIntro p q (K'.ifIntro p q pq) (K'.ifIntro q p qp)

class IffForw {P : Sort u} (L : Logic P) (Iff : LIff P) (If : LIf P) := 
  (iffForw : (p q : P) -> (L |- p <-> q) -> (L |- p -> q))

def iffForw {P : Sort u} {L : Logic P} [Iff : LIff P] [If : LIf P]
  [K : IffForw L Iff If] {p q : P} := K.iffForw p q

def iffForw' {P : Sort u} {L : Logic P} [Iff : LIff P] [If : LIf P] 
  [K : IffForw L Iff If] [K' : IfElim L If] {p q : P} 
  : (L |- p <-> q) -> ((L |- p) -> (L |- q))
  := fun pIff => K'.ifElim p q (K.iffForw p q pIff)

class IffBack {P : Sort u} (L : Logic P) (Iff : LIff P) (If : LIf P) := 
  iffBack : (p q : P) -> (L |- p <-> q) -> (L |- q -> p)

def iffBack {P : Sort u} {L : Logic P} [Iff : LIff P] [If : LIf P]
  [K : IffBack L Iff If] {p q : P} := K.iffBack p q

def iffBack' {P : Sort u} {L : Logic P} [Iff : LIff P] [If : LIf P] 
  [K : IffBack L Iff If] [K' : IfElim L If] {p q : P} 
  : (L |- p <-> q) -> ((L |- q) -> (L |- p))
  := fun pIff => K'.ifElim q p (K.iffBack p q pIff)

--------------------------------------------------------------------------------
-- Conjuction
--------------------------------------------------------------------------------

-- p, q |- p /\ q

class ConjIntro {P : Sort u} (L : Logic P) (Cj : Conj P) := 
  conjIntro : (p q : P) -> (L |- p) -> (L |- q) -> (L |- p /\ q) 

def conjIntro {P : Sort u} {L : Logic P} [Cj : Conj P] 
  [K : ConjIntro L Cj] {p q : P} := K.conjIntro p q

-- p /\ q -> p

class ConjLeft {P : Sort u} (L : Logic P) (Cj : Conj P) := 
  conjLeft : (p q : P) -> (L |- p /\ q) -> (L |- p)

def conjLeft {P : Sort u} {L : Logic P} [Cj : Conj P] 
  [K : ConjLeft L Cj] {p q : P} := K.conjLeft p q

-- p /\ q -> q

class ConjRight {P : Sort u} (L : Logic P) (Cj : Conj P) := 
  conjRight : (p q : P) -> (L |- p /\ q) -> (L |- q)

def conjRight {P : Sort u} {L : Logic P} [Cj : Conj P] 
  [K : ConjRight L Cj] {p q : P} := K.conjRight p q

-- p /\ q -> p

class ConjElim {P : Sort u} (L : Logic P) (Cj : Conj P) := 
  conjElim : (p q : P) -> (L |- p /\ q) -> PProd (L |- p) (L |- q)

def conjElim {P : Sort u} {L : Logic P} [Cj : Conj P] 
  [K : ConjElim L Cj] {p q : P} := K.conjElim p q

instance iConjElimOfLeftRight {P : Sort u} {L : Logic P} [Cj : Conj P]
  [CjL : ConjLeft L Cj] [CjR : ConjRight L Cj] : ConjElim L Cj := 
  {conjElim := fun p q LpCq => PProd.mk (conjLeft LpCq) (conjRight LpCq)}

instance iConjLeftOfElim {P : Sort u} {L : Logic P} [Cj : Conj P]
  [K : ConjElim L Cj] : ConjLeft L Cj := 
  {conjLeft := fun p q LpCq => PProd.fst (K.conjElim p q LpCq)}

instance iConjRightOfElim {P : Sort u} {L : Logic P} [Cj : Conj P]
  [K : ConjElim L Cj] : ConjRight L Cj := 
  {conjRight := fun p q LpCq => PProd.snd (K.conjElim p q LpCq)}

-- p -> p /\ p

class ConjTaut {P : Sort u} (L : Logic P) (Cj : Conj P)  :=
  conjTaut : (p : P) -> (L |- p) -> (L |- p /\ p)

def conjTaut {P : Sort u} {L : Logic P} [Cj : Conj P] 
  [K : ConjTaut L Cj] {p : P} := K.conjTaut p

instance iConjTautOfIntro {P : Sort u} {L : Logic P} [Cj : Conj P]
  [K : ConjIntro L Cj] : ConjTaut L Cj := 
  {conjTaut := fun p Lp => K.conjIntro p p Lp Lp}

-- p /\ p -> p

class ConjSimp {P : Sort u} (L : Logic P) (Cj : Conj P)  :=
  conjSimp : (p : P) -> (L |- p /\ p) -> (L |- p)

def conjSimp {P : Sort u} {L : Logic P} [Cj : Conj P] 
  [K : ConjSimp L Cj] {p : P} := K.conjSimp p

instance iConjSimpOfLeft {P : Sort u} {L : Logic P} [Cj : Conj P]
  [K : ConjLeft L Cj] : ConjSimp L Cj := 
  {conjSimp := fun p LpCq => K.conjLeft p p LpCq}

instance iConjSimpOfRight {P : Sort u} {L : Logic P} [Cj : Conj P]
  [K : ConjRight L Cj] : ConjSimp L Cj := 
  {conjSimp := fun p LpCq => K.conjRight p p LpCq}

-- (p /\ q -> a) -> (p -> q -> a)

class ConjCurry {P : Sort u} (L : Logic P) (Cj : Conj P) :=
  conjCurry : (a : Sort v) -> (p q : P) -> 
    ((L |- p /\ q) -> a) -> ((L |- p) -> (L |- q) -> a)

def conjCurry {P : Sort u} {L : Logic P} [Cj : Conj P] 
  [K : ConjCurry L Cj] {a : Sort v} {p q : P} := K.conjCurry a p q

instance iConjCurryOfIntro {P : Sort u} {L : Logic P} [Cj : Conj P]
  [CjI : ConjIntro L Cj] : ConjCurry L Cj := 
  {conjCurry := fun a p q fpCq Lp Lq  => fpCq (conjIntro Lp Lq)}

-- (p -> q -> a) -> (p /\ q -> a)

class ConjUncurry {P : Sort u} (L : Logic P) (Cj : Conj P) :=
  conjUncurry : (a : Sort v) -> (p q : P) -> 
    ((L |- p) -> (L |- q) -> a) -> ((L |- p /\ q) -> a)

def conjUncurry {P : Sort u} {L : Logic P} [Cj : Conj P] 
  [K : ConjUncurry L Cj] {a : Sort v} {p q : P} := K.conjUncurry a p q

instance iConjUncurryOfElim {P : Sort u} {L : Logic P} [Cj : Conj P]
  [K : ConjElim L Cj] : ConjUncurry L Cj := 
  {conjUncurry := fun a p q fpq LpCq => fpq (conjLeft LpCq) (conjRight LpCq)}

--------------------------------------------------------------------------------
-- Disjunction
--------------------------------------------------------------------------------

-- q -> p \/ q

class DisjIntroLeft {P : Sort u} (L : Logic P) (Dj : Disj P)  := 
  disjIntroLeft : (p q : P) -> (L |- q) -> (L |- p \/ q) 

def disjIntroLeft {P : Sort u} {L : Logic P} [Dj : Disj P] 
  [K : DisjIntroLeft L Dj] {p q : P} := K.disjIntroLeft p q

-- p -> p \/ q

class DisjIntroRight {P : Sort u} (L : Logic P) (Dj : Disj P)  := 
  disjIntroRight : (p q : P) -> (L |- p) -> (L |- p \/ q) 

def disjIntroRight {P : Sort u} {L : Logic P} [Dj : Disj P] 
  [K : DisjIntroRight L Dj] {p q : P} := K.disjIntroRight p q

-- p -> p \/ p

class DisjTaut {P : Sort u} (L : Logic P) (Dj : Disj P) :=
  disjTaut : (p : P) -> (L |- p) -> (L |- p \/ p)

def disjTaut {P : Sort u} {L : Logic P} [Dj : Disj P] 
  [K : DisjTaut L Dj] {p : P} := K.disjTaut p

instance iDisjTautOfIntroLeft {P : Sort u} {L : Logic P} [Dj : Disj P]
  [K : DisjIntroLeft L Dj] : DisjTaut L Dj := 
  {disjTaut := fun p Lp => K.disjIntroLeft p p Lp}

instance iDisjTautOfIntroRight {P : Sort u} {L : Logic P} [Dj : Disj P]
  [K : DisjIntroRight L Dj] : DisjTaut L Dj := 
  {disjTaut := fun p Lp => K.disjIntroRight p p Lp}

-- p \/ q -> (p -> r) -> (q -> r) -> r

class DisjElim {P : Sort u} (L : Logic P) (Dj : Disj P) := 
  disjElim : (p q r : P) -> (L |- p \/ q) -> 
    ((L |- p) -> (L |- r)) -> ((L |- q) -> (L |- r)) -> (L |- r)

def disjElim {P : Sort u} {L : Logic P} [Dj : Disj P]
  [K : DisjElim L Dj] {p q r : P} := K.disjElim p q r

-- p \/ p -> p

class DisjSimp {P : Sort u} (L : Logic P) (Dj : Disj P) :=
  disjSimp : (p : P) -> (L |- p \/ p) -> (L |- p)

def disjSimp {P : Sort u} {L : Logic P} [Dj : Disj P] 
  [K : DisjSimp L Dj] {p : P} := K.disjSimp p

instance iDisjSimpOfDisjElim {P : Sort u} {L : Logic P} [Dj : Disj P]
  [K : DisjElim L Dj] : DisjSimp L Dj := 
  {disjSimp := fun p LpDp => K.disjElim p p p LpDp id id}

-- p \/ q -> ~p -> q

class DisjElimLeft {P : Sort u} (L : Logic P) (Dj : Disj P) (Nt : LNot P) := 
  disjElimLeft : (p q : P) -> (L |- p \/ q) -> (L |- ~p) -> (L |- q)

def disjElimLeft {P : Sort u} {L : Logic P} [Dj : Disj P] [Nt : LNot P] 
  [K : DisjElimLeft L Dj Nt] {p q : P} := K.disjElimLeft p q

-- p \/ q -> ~q -> p

class DisjElimRight {P : Sort u} (L : Logic P) (Dj : Disj P) (Nt : LNot P) := 
  disjElimRight : (p q : P) -> (L |- p \/ q) -> (L |- ~q) -> (L |- p)

def disjElimRight {P : Sort u} {L : Logic P} [Dj : Disj P] [Nt : LNot P] 
  [K : DisjElimRight L Dj Nt] {p q : P} := K.disjElimRight p q

--------------------------------------------------------------------------------
-- Not
--------------------------------------------------------------------------------

class NotIntro {P : Sort u} (L : Logic P) (Nt : LNot P) (F : LFalse P) := 
  notIntro : (p : P) -> ((L |- p) -> (L |- false)) -> (L |- ~p) 

def notIntro {P : Sort u} {L : Logic P} [Nt : LNot P] [F : LFalse P] 
  [K : NotIntro L Nt F] {p : P} := K.notIntro p

class NotElim {P : Sort u} (L : Logic P) (Nt : LNot P) (F : LFalse P) := 
  notElim : (p : P) -> (L |- ~p) -> ((L |- p) -> (L |- false))

def notElim {P : Sort u} {L : Logic P} [Nt : LNot P] [F : LFalse P] 
  [K : NotElim L Nt F] {p : P} := K.notElim p

--------------------------------------------------------------------------------
-- True
--------------------------------------------------------------------------------

class TrueIntro {P : Sort u} (L : Logic P) (T : LTrue P) := 
  (trueIntro : L |- true) 

def trueIntro {P : Sort u} {L : Logic P} [T : LTrue P]
  [K : TrueIntro L T] := K.trueIntro

end Gaea.Logic