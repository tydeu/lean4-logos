import Gaea.Logic.Notation

universes u v w
variable {P : Sort u} {T : Sort v}

namespace Gaea.Logic

--------------------------------------------------------------------------------
-- Forall
--------------------------------------------------------------------------------

class ForallIntro (L : Logic P) (Fa : LForall P T) := 
  forallIntro : (f : T -> P) -> ((a : T) -> (L |- f a)) -> (L |- lForall f)

def forallIntro {L : Logic P} [Fa : LForall P T]  
  [K : ForallIntro L Fa] {f} := K.forallIntro f

class ForallElim (L : Logic P) (Fa : LForall P T) := 
  forallElim : (f : T -> P) -> (L |- lForall f) -> ((a : T) -> (L |- f a))  

def forallElim {L : Logic P} [Fa : LForall P T]  
  [K : ForallElim L Fa] {f} := K.forallElim f

--------------------------------------------------------------------------------
-- Exists
--------------------------------------------------------------------------------

class ExistsIntro (L : Logic P) (X : LExists P T) := 
  existsIntro : (f : T -> P) -> (a : T) -> (L |- f a) -> (L |- lExists f)

def existsIntro {L : Logic P} [X : LExists P T]  
  [K : ExistsIntro L X] {f} := K.existsIntro f

class ExistsElim (L : Logic P) (X : LExists P T) := 
  existsElim : (r : Sort w) -> (f : T -> P) ->  (L |- lExists f) -> 
    ((a : T) -> (L |- f a) -> r) -> r

def existsElim {L : Logic P} [X : LExists P T]  
  [K : ExistsElim L X] {r f} := K.existsElim r f

--------------------------------------------------------------------------------
-- If
--------------------------------------------------------------------------------

-- ((L |- p) -> (L |- q)) -> (L |- p -> q) 

class IfIntro (L : Logic P) (If : LIf P) := 
  ifIntro : (p q : P) -> ((L |- p) -> (L |- q)) -> (L |- p -> q) 

def ifIntro {L : Logic P} [If : LIf P] [K : IfIntro L If] 
  {p q} := K.ifIntro p q

-- (L |- p -> q) -> ((L |- p) -> (L |- q))

class IfElim (L : Logic P) (If : LIf P) := 
  ifElim : (p q : P) -> (L |- p -> q) -> ((L |- p) -> (L |- q))

def ifElim {L : Logic P} [If : LIf P] [K : IfElim L If] 
  {p q} := K.ifElim p q

--------------------------------------------------------------------------------
-- Iff
--------------------------------------------------------------------------------

-- (L |- p -> q) -> (L |- q -> p) -> (L |- p <-> q)

class IffIntro (L : Logic P) (Iff : LIff P) (If : LIf P) := 
  iffIntro : (p q : P) -> (L |- p -> q) -> (L |- q -> p) -> (L |- p <-> q)

def iffIntro {L : Logic P} [Iff : LIff P] [If : LIf P]
  [K : IffIntro L Iff If] {p q} := K.iffIntro p q

def iffIntro' {L : Logic P} [Iff : LIff P] [If : LIf P] 
  [K : IffIntro L Iff If] [IfI : IfIntro L If] {p q} 
  : ((L |- p) -> (L |- q)) -> ((L |- q) -> (L |- p)) -> (L |- p <-> q)
  := fun pq qp => K.iffIntro p q (IfI.ifIntro p q pq) (IfI.ifIntro q p qp)

-- (L |- p <-> q) -> (L |- p -> q)

class IffForw (L : Logic P) (Iff : LIff P) (If : LIf P) := 
  iffForw : (p q : P) -> (L |- p <-> q) -> (L |- p -> q)

def iffForw {L : Logic P} [Iff : LIff P] [If : LIf P]
  [K : IffForw L Iff If] {p q} := K.iffForw p q

def iffForw' {L : Logic P} [Iff : LIff P] [If : LIf P] 
  [K : IffForw L Iff If] [K' : IfElim L If] {p q} 
  : (L |- p <-> q) -> ((L |- p) -> (L |- q))
  := fun pIff => K'.ifElim p q (K.iffForw p q pIff)

-- (L |- p <-> q) -> (L |- q -> p)

class IffBack (L : Logic P) (Iff : LIff P) (If : LIf P) := 
  iffBack : (p q : P) -> (L |- p <-> q) -> (L |- q -> p)

def iffBack {L : Logic P} [Iff : LIff P] [If : LIf P]
  [K : IffBack L Iff If] {p q} := K.iffBack p q

def iffBack' {L : Logic P} [Iff : LIff P] [If : LIf P] 
  [K : IffBack L Iff If] [IfE : IfElim L If] {p q} 
  : (L |- p <-> q) -> ((L |- q) -> (L |- p))
  := fun pIff => IfE.ifElim q p (K.iffBack p q pIff)

--------------------------------------------------------------------------------
-- Conjuction
--------------------------------------------------------------------------------

-- p, q |- p /\ q

class ConjIntro (L : Logic P) (Cj : Conj P) := 
  conjIntro : (p q : P) -> (L |- p) -> (L |- q) -> (L |- p /\ q) 

def conjIntro {L : Logic P} [Cj : Conj P] 
  [K : ConjIntro L Cj] {p q} := K.conjIntro p q

-- p /\ q -> p

class ConjLeft (L : Logic P) (Cj : Conj P) := 
  conjLeft : (p q : P) -> (L |- p /\ q) -> (L |- p)

def conjLeft {L : Logic P} [Cj : Conj P] 
  [K : ConjLeft L Cj] {p q} := K.conjLeft p q

-- p /\ q -> q

class ConjRight (L : Logic P) (Cj : Conj P) := 
  conjRight : (p q : P) -> (L |- p /\ q) -> (L |- q)

def conjRight {L : Logic P} [Cj : Conj P] 
  [K : ConjRight L Cj] {p q} := K.conjRight p q

-- p -> p /\ p

class ConjTaut (L : Logic P) (Cj : Conj P)  :=
  conjTaut : (p : P) -> (L |- p) -> (L |- p /\ p)

def conjTaut {L : Logic P} [Cj : Conj P] 
  [K : ConjTaut L Cj] {p} := K.conjTaut p

instance iConjTautOfIntro {L : Logic P} [Cj : Conj P]
  [K : ConjIntro L Cj] : ConjTaut L Cj := 
  {conjTaut := fun p Lp => K.conjIntro p p Lp Lp}

-- p /\ p -> p

class ConjSimp (L : Logic P) (Cj : Conj P)  :=
  conjSimp : (p : P) -> (L |- p /\ p) -> (L |- p)

def conjSimp {L : Logic P} [Cj : Conj P] 
  [K : ConjSimp L Cj] {p} := K.conjSimp p

instance iConjSimpOfLeft {L : Logic P} [Cj : Conj P]
  [K : ConjLeft L Cj] : ConjSimp L Cj := 
  {conjSimp := fun p LpCq => K.conjLeft p p LpCq}

instance iConjSimpOfRight {L : Logic P} [Cj : Conj P]
  [K : ConjRight L Cj] : ConjSimp L Cj := 
  {conjSimp := fun p LpCq => K.conjRight p p LpCq}

-- (p /\ q -> a) -> (p -> q -> a)

class ConjCurry (L : Logic P) (Cj : Conj P) :=
  conjCurry : (r : Sort w) -> (p q : P) -> 
    ((L |- p /\ q) -> r) -> ((L |- p) -> (L |- q) -> r)

def conjCurry {L : Logic P} [Cj : Conj P] 
  [K : ConjCurry L Cj] {r p q} := K.conjCurry r p q

instance iConjCurryOfIntro {L : Logic P} [Cj : Conj P]
  [CjI : ConjIntro L Cj] : ConjCurry L Cj := 
  {conjCurry := fun a p q fpCq Lp Lq  => fpCq (conjIntro Lp Lq)}

-- (p -> q -> a) -> (p /\ q -> a)

class ConjUncurry (L : Logic P) (Cj : Conj P) :=
  conjUncurry : (r : Sort w) -> (p q : P) -> 
    ((L |- p) -> (L |- q) -> r) -> ((L |- p /\ q) -> r)

def conjUncurry {L : Logic P} [Cj : Conj P] 
  [K : ConjUncurry L Cj] {r p q} := K.conjUncurry r p q

instance iConjUncurryOfLeftRight {L : Logic P} [Cj : Conj P]
  [CjL : ConjLeft L Cj] [CjR : ConjRight L Cj] : ConjUncurry L Cj := 
  {conjUncurry := fun a p q fpq LpCq => fpq (conjLeft LpCq) (conjRight LpCq)}

-- Prod p q -> p /\ q 

class ConjOfProd (L : Logic P) (Cj : Conj P) := 
  conjOfProd : (p q : P) -> Prod (L |- p) (L |- q) -> (L |- p /\ q)

def conjOfProd {L : Logic P} [Cj : Conj P] 
  [K : ConjOfProd L Cj] {p q} := K.conjOfProd p q

instance iConjIntroOfProd {L : Logic P} [Cj : Conj P] 
  [K : ConjOfProd L Cj] : ConjIntro L Cj := 
  {conjIntro := fun p q Lp Lq => K.conjOfProd p q (Prod.mk Lp Lq)}

instance iConjOfProdOfIntro {L : Logic P} [Cj : Conj P] 
  [K : ConjIntro L Cj] : ConjOfProd L Cj := 
  {conjOfProd := fun p q Ppq => K.conjIntro p q Ppq.fst Ppq.snd}

-- PProd p q -> p /\ q 

class ConjOfPProd (L : Logic P) (Cj : Conj P) := 
  conjOfPProd : (p q : P) -> PProd (L |- p) (L |- q) -> (L |- p /\ q)

def conjOfPProd {L : Logic P} [Cj : Conj P] 
  [K : ConjOfPProd L Cj] {p q} := K.conjOfPProd p q

instance iConjIntroOfPProd {L : Logic P} [Cj : Conj P] 
  [K : ConjOfPProd L Cj] : ConjIntro L Cj := 
  {conjIntro := fun p q Lp Lq => K.conjOfPProd p q (PProd.mk Lp Lq)}

instance iConjOfPProdOfIntro {L : Logic P} [Cj : Conj P] 
  [K : ConjIntro L Cj] : ConjOfPProd L Cj := 
  {conjOfPProd := fun p q Ppq => K.conjIntro p q Ppq.fst Ppq.snd}

instance iConjOfProdOfPProd {L : Logic P} [Cj : Conj P] 
  [K : ConjOfPProd L Cj] : ConjOfProd L Cj := 
  {conjOfProd := fun p q Ppq => K.conjOfPProd p q (PProd.mk (Ppq.fst) (Ppq.snd))}

-- And p q -> p /\ q 

class ConjOfAnd (L : Logic P) (Cj : Conj P) := 
  conjOfAnd : (p q : P) -> (L |- p) /\ (L |- q) -> (L |- p /\ q)

def conjOfAnd {L : Logic P} [Cj : Conj P] 
  [K : ConjOfAnd L Cj] {p q} := K.conjOfAnd p q

instance iConjIntroOfAnd {L : Logic P} [Cj : Conj P] 
  [K : ConjOfAnd L Cj] : ConjIntro L Cj := 
  {conjIntro := fun p q Lp Lq => K.conjOfAnd p q (And.intro Lp Lq)}

instance iConjOfAndOfIntro {L : Logic P} [Cj : Conj P] 
  [K : ConjIntro L Cj] : ConjOfAnd L Cj := 
  {conjOfAnd := fun p q Apq => K.conjIntro p q Apq.left Apq.right}

-- p /\ q -> Prod p q

class ConjAsProd (L : Logic P) (Cj : Conj P) := 
  conjAsProd : (p q : P) -> (L |- p /\ q) -> Prod (L |- p) (L |- q)

def conjAsProd {L : Logic P} [Cj : Conj P] 
  [K : ConjAsProd L Cj] {p q} := K.conjAsProd p q

instance iConjAsProdOfLeftRight {L : Logic P} [Cj : Conj P]
  [CjL : ConjLeft L Cj] [CjR : ConjRight L Cj] : ConjAsProd L Cj := 
  {conjAsProd := fun p q LpCq => Prod.mk (conjLeft LpCq) (conjRight LpCq)}

instance iConjLeftOfAsProd {L : Logic P} [Cj : Conj P]
  [K : ConjAsProd L Cj] : ConjLeft L Cj := 
  {conjLeft := fun p q LpCq => Prod.fst (K.conjAsProd p q LpCq)}

instance iConjRightOfAsProd {L : Logic P} [Cj : Conj P]
  [K : ConjAsProd L Cj] : ConjRight L Cj := 
  {conjRight := fun p q LpCq => Prod.snd (K.conjAsProd p q LpCq)}

-- p /\ q -> PProd p q

class ConjAsPProd (L : Logic P) (Cj : Conj P) := 
  conjAsPProd : (p q : P) -> (L |- p /\ q) -> PProd (L |- p) (L |- q)

def conjAsPProd {L : Logic P} [Cj : Conj P] 
  [K : ConjAsPProd L Cj] {p q} := K.conjAsPProd p q

instance iConjAsPProdOfLeftRight {L : Logic P} [Cj : Conj P]
  [CjL : ConjLeft L Cj] [CjR : ConjRight L Cj] : ConjAsPProd L Cj := 
  {conjAsPProd := fun p q LpCq => PProd.mk (conjLeft LpCq) (conjRight LpCq)}

instance iConjLeftOfAsPProd {L : Logic P} [Cj : Conj P]
  [K : ConjAsPProd L Cj] : ConjLeft L Cj := 
  {conjLeft := fun p q LpCq => PProd.fst (K.conjAsPProd p q LpCq)}

instance iConjRightOfAsPProd {L : Logic P} [Cj : Conj P]
  [K : ConjAsPProd L Cj] : ConjRight L Cj := 
  {conjRight := fun p q LpCq => PProd.snd (K.conjAsPProd p q LpCq)}

instance iConjAsProdOfPProd {L : Logic P} [Cj : Conj P]
  [K : ConjAsPProd L Cj] : ConjAsProd L Cj := 
  {conjAsProd := fun p q LpCq => Prod.mk (conjLeft LpCq) (conjRight LpCq)}

-- p /\ q -> And p q

class ConjAsAnd (L : Logic P) (Cj : Conj P) := 
  conjAsAnd : (p q : P) -> (L |- p /\ q) -> (L |- p) /\ (L |- q)

def conjAsAnd {L : Logic P} [Cj : Conj P] 
  [K : ConjAsAnd L Cj] {p q} := K.conjAsAnd p q

instance iConjAsAndOfLeftRight {L : Logic P} [Cj : Conj P]
  [CjL : ConjLeft L Cj] [CjR : ConjRight L Cj] : ConjAsAnd L Cj := 
  {conjAsAnd := fun p q LpCq => And.intro (conjLeft LpCq) (conjRight LpCq)}

instance iConjLeftOfAsAnd {L : Logic P} [Cj : Conj P]
  [K : ConjAsAnd L Cj] : ConjLeft L Cj := 
  {conjLeft := fun p q LpCq => And.left (K.conjAsAnd p q LpCq)}

instance iConjRightOfAsAnd {L : Logic P} [Cj : Conj P]
  [K : ConjAsAnd L Cj] : ConjRight L Cj := 
  {conjRight := fun p q LpCq => And.right (K.conjAsAnd p q LpCq)}

--------------------------------------------------------------------------------
-- Disjunction
--------------------------------------------------------------------------------

-- p -> p \/ q

class DisjIntroLeft (L : Logic P) (Dj : Disj P)  := 
  disjIntroLeft : (p q : P) -> (L |- p) -> (L |- p \/ q) 

def disjIntroLeft {L : Logic P} [Dj : Disj P] 
  [K : DisjIntroLeft L Dj] {p q} := K.disjIntroLeft p q

-- q -> p \/ q

class DisjIntroRight (L : Logic P) (Dj : Disj P)  := 
  disjIntroRight : (p q : P) -> (L |- q) -> (L |- p \/ q) 

def disjIntroRight {L : Logic P} [Dj : Disj P] 
  [K : DisjIntroRight L Dj] {p q} := K.disjIntroRight p q

-- p \/ q -> (p -> r) -> (q -> r) -> r

class DisjElim (L : Logic P) (Dj : Disj P) := 
  disjElim : (r : Sort w) -> (p q : P) -> 
    (L |- p \/ q) -> ((L |- p) -> r) -> ((L |- q) -> r) -> r

def disjElim {L : Logic P} [Dj : Disj P]
  [K : DisjElim L Dj] {r p q} := K.disjElim r p q

-- p -> p \/ p

class DisjTaut (L : Logic P) (Dj : Disj P) :=
  disjTaut : (p : P) -> (L |- p) -> (L |- p \/ p)

def disjTaut {L : Logic P} [Dj : Disj P] 
  [K : DisjTaut L Dj] {p} := K.disjTaut p

instance iDisjTautOfIntroLeft {L : Logic P} [Dj : Disj P]
  [K : DisjIntroLeft L Dj] : DisjTaut L Dj := 
  {disjTaut := fun p Lp => K.disjIntroLeft p p Lp}

instance iDisjTautOfIntroRight {L : Logic P} [Dj : Disj P]
  [K : DisjIntroRight L Dj] : DisjTaut L Dj := 
  {disjTaut := fun p Lp => K.disjIntroRight p p Lp}

-- p \/ p -> p

class DisjSimp (L : Logic P) (Dj : Disj P) :=
  disjSimp : (p : P) -> (L |- p \/ p) -> (L |- p)

def disjSimp {L : Logic P} [Dj : Disj P] 
  [K : DisjSimp L Dj] {p} := K.disjSimp p

instance iDisjSimpOfElim {L : Logic P} [Dj : Disj P]
  [K : DisjElim L Dj] : DisjSimp L Dj := 
  {disjSimp := fun p LpDp => K.disjElim _ p p LpDp id id}

-- p \/ q -> ~p -> q

class DisjElimLeft (L : Logic P) (Dj : Disj P) (Nt : LNot P) := 
  disjElimLeft : (p q : P) -> (L |- p \/ q) -> (L |- ~p) -> (L |- q)

def disjElimLeft {L : Logic P} [Dj : Disj P] [Nt : LNot P] 
  [K : DisjElimLeft L Dj Nt] {p q} := K.disjElimLeft p q

-- p \/ q -> ~q -> p

class DisjElimRight (L : Logic P) (Dj : Disj P) (Nt : LNot P) := 
  disjElimRight : (p q : P) -> (L |- p \/ q) -> (L |- ~q) -> (L |- p)

def disjElimRight {L : Logic P} [Dj : Disj P] [Nt : LNot P] 
  [K : DisjElimRight L Dj Nt] {p q} := K.disjElimRight p q

-- Sum p q -> p \/ q 

class DisjOfSum (L : Logic P) (Dj : Disj P) := 
  disjOfSum : (p q : P) -> Sum (L |- p) (L |- q) -> (L |- p \/ q)

def disjOfSum {L : Logic P} [Dj : Disj P] 
  [K : DisjOfSum L Dj] {p q} := K.disjOfSum p q

instance iDisjOfSumOfIntro {L : Logic P} [Dj : Disj P] 
  [DiL : DisjIntroLeft L Dj] [DiR : DisjIntroRight L Dj] : DisjOfSum L Dj := 
  {disjOfSum := fun p q Spq => match Spq with 
    | Sum.inl Lp => disjIntroLeft Lp | Sum.inr Lq => disjIntroRight Lq}

instance iDisjIntroLeftOfSum {L : Logic P} [Dj : Disj P] 
  [K : DisjOfSum L Dj] : DisjIntroLeft L Dj := 
  {disjIntroLeft := fun p q Lp => K.disjOfSum p q (Sum.inl Lp)}

instance iDisjIntroRightOfSum {L : Logic P} [Dj : Disj P] 
  [K : DisjOfSum L Dj] : DisjIntroRight L Dj := 
  {disjIntroRight := fun p q Lq => K.disjOfSum p q (Sum.inr Lq)}

-- PSum p q -> p \/ q  

class DisjOfPSum (L : Logic P) (Dj : Disj P) := 
  disjOfPSum : (p q : P) -> PSum (L |- p) (L |- q) -> (L |- p \/ q)

def disjOfPSum {L : Logic P} [Dj : Disj P] 
  [K : DisjOfPSum L Dj] {p q} := K.disjOfPSum p q

instance iDisjOfPSumOfIntro {L : Logic P} [Dj : Disj P] 
  [DiL : DisjIntroLeft L Dj] [DiR : DisjIntroRight L Dj] : DisjOfPSum L Dj := 
  {disjOfPSum := fun p q Spq => match Spq with 
    | PSum.inl Lp => disjIntroLeft Lp | PSum.inr Lq => disjIntroRight Lq}

instance iDisjIntroLeftOfPSum {L : Logic P} [Dj : Disj P] 
  [K : DisjOfPSum L Dj] : DisjIntroLeft L Dj := 
  {disjIntroLeft := fun p q Lp => K.disjOfPSum p q (PSum.inl Lp)}

instance iDisjIntroRightOfPSum {L : Logic P} [Dj : Disj P] 
  [K : DisjOfPSum L Dj] : DisjIntroRight L Dj := 
  {disjIntroRight := fun p q Lq => K.disjOfPSum p q (PSum.inr Lq)}

-- Or p q -> p \/ q 

class DisjOfOr (L : Logic P) (Dj : Disj P) := 
  disjOfOr : (p q : P) -> (L |- p) \/ (L |- q) -> (L |- p \/ q)

def disjOfOr {L : Logic P} [Dj : Disj P] 
  [K : DisjOfOr L Dj] {p q} := K.disjOfOr p q

instance iDisjOfOrOfIntro {L : Logic P} [Dj : Disj P] 
  [DiL : DisjIntroLeft L Dj] [DiR : DisjIntroRight L Dj] : DisjOfOr L Dj := 
  {disjOfOr := fun p q Spq => match Spq with 
    | Or.inl Lp => disjIntroLeft Lp | Or.inr Lq => disjIntroRight Lq}

instance iDisjIntroLeftOfOr {L : Logic P} [Dj : Disj P] 
  [K : DisjOfOr L Dj] : DisjIntroLeft L Dj := 
  {disjIntroLeft := fun p q Lp => K.disjOfOr p q (Or.inl Lp)}

instance iDisjIntroRightOfOr {L : Logic P} [Dj : Disj P] 
  [K : DisjOfOr L Dj] : DisjIntroRight L Dj := 
  {disjIntroRight := fun p q Lq => K.disjOfOr p q (Or.inr Lq)}

-- p \/ q  -> Sum p q 

class DisjAsSum (L : Logic P) (Dj : Disj P) := 
  disjAsSum : (p q : P) -> (L |- p \/ q) -> Sum (L |- p) (L |- q)

def disjAsSum {L : Logic P} [Dj : Disj P] 
  [K : DisjAsSum L Dj] {p q} := K.disjAsSum p q

instance iDisjAsSumOfElim {L : Logic P} [Dj : Disj P] 
  [K : DisjElim L Dj] : DisjAsSum L Dj := 
  {disjAsSum := fun p q LpDq => K.disjElim _ p q LpDq Sum.inl Sum.inr}

instance iDisjElimOfAsSum {L : Logic P} [Dj : Disj P] 
  [K : DisjAsSum L Dj] : DisjElim L Dj := 
  {disjElim := fun a p q LpDq fpa fqa => match K.disjAsSum p q LpDq with
    | Sum.inl Lp => fpa Lp | Sum.inr Lq => fqa Lq}

-- p \/ q  -> PSum p q 

class DisjAsPSum (L : Logic P) (Dj : Disj P) := 
  disjAsPSum : (p q : P) -> (L |- p \/ q) -> PSum (L |- p) (L |- q)

def disjAsPSum {L : Logic P} [Dj : Disj P] 
  [K : DisjAsPSum L Dj] {p q} := K.disjAsPSum p q

instance iDisjAsPSumOfElim {L : Logic P} [Dj : Disj P] 
  [K : DisjElim L Dj] : DisjAsPSum L Dj := 
  {disjAsPSum := fun p q LpDq => K.disjElim _ p q LpDq PSum.inl PSum.inr}

instance iDisjElimOfAsPSum {L : Logic P} [Dj : Disj P] 
  [K : DisjAsPSum L Dj] : DisjElim L Dj := 
  {disjElim := fun a p q LpDq fpa fqa => match K.disjAsPSum p q LpDq with
    | PSum.inl Lp => fpa Lp | PSum.inr Lq => fqa Lq}

-- p \/ q  -> Or p q 

class DisjAsOr (L : Logic P) (Dj : Disj P) := 
  disjAsOr : (p q : P) -> (L |- p \/ q) -> (L |- p) \/ (L |- q)

def disjAsOr {L : Logic P} [Dj : Disj P] 
  [K : DisjAsOr L Dj] {p q} := K.disjAsOr p q

instance iDisjAsOrOfElim {L : Logic P} [Dj : Disj P] 
  [K : DisjElim L Dj] : DisjAsOr L Dj := 
  {disjAsOr := fun p q LpDq => K.disjElim _ p q LpDq Or.inl Or.inr}

instance iDisjElimOfAsOr {L : Logic P} [Dj : Disj P] 
  [K : DisjAsOr L Dj] : DisjElim L Dj := 
  {disjElim := fun (a : Prop) p q LpDq fpa fqa => match K.disjAsOr p q LpDq with
    | Or.inl Lp => fpa Lp | Or.inr Lq => fqa Lq}

--------------------------------------------------------------------------------
-- Not
--------------------------------------------------------------------------------

class NotIntro (L : Logic P) (Nt : LNot P) := 
  notIntro : (p : P) -> ((L |- p) -> False) -> (L |- ~p) 

def notIntro {L : Logic P} [Nt : LNot P]
  [K : NotIntro L Nt] {p} := K.notIntro p

class NotElim (L : Logic P) (Nt : LNot P) := 
  notElim : (p : P) -> (L |- ~p) -> ((L |- p) -> False)

def notElim {L : Logic P} [Nt : LNot P] 
  [K : NotElim L Nt] {p} := K.notElim p

--------------------------------------------------------------------------------
-- True
--------------------------------------------------------------------------------

class TrueIntro (L : Logic P) (T : LTrue P) := 
  trueIntro : L |- true 

def trueIntro {L : Logic P} [T : LTrue P]
  [K : TrueIntro L T] := K.trueIntro

--------------------------------------------------------------------------------
-- Contradiction
--------------------------------------------------------------------------------

def Contradiction (L : Logic P) (Nt : LNot P) :=
  PSigma fun (p : P) => PProd (L |- p) (L |- ~p)

def contradiction {L : Logic P} [Nt : LNot P]
  {p} (Lp : L |- p) (LNp : L |- ~p) : Contradiction L Nt := 
    PSigma.mk p (PProd.mk Lp LNp)

class ByContradiction (L : Logic P) (Nt : LNot P) :=
  byContradiction : (p : P) -> ((L |- p) -> Contradiction L Nt) -> (L |- ~p)

def byContradiction {L : Logic P} [Nt : LNot P]
  [K : ByContradiction L Nt] {p} := K.byContradiction p

--------------------------------------------------------------------------------
-- Absurdity
--------------------------------------------------------------------------------

class Absurdity (L : Logic P) :=
  absurdity : Sort w

def absurdity (L : Logic P) [K : Absurdity L] 
  := K.absurdity L

class AdAbsurdium (L : Logic P) (A : Absurdity L) (Nt : LNot P) :=
  adAbsurdium : (p : P) -> ((L |- p) -> absurdity L) -> (L |- ~p)

def adAbsurdium {L : Logic P} [A : Absurdity L] [Nt : LNot P]
  [K : AdAbsurdium L A Nt] {p} := K.adAbsurdium p

class ExAbsurdium (L : Logic P) (A : Absurdity L) :=
  exAbsurdium : (p : P) -> absurdity L -> (L |- p)

def exAbsurdium {L : Logic P} [A : Absurdity L]
  [K : ExAbsurdium L A] {p} := K.exAbsurdium p

--------------------------------------------------------------------------------
-- False
--------------------------------------------------------------------------------

class FalseIntro (L : Logic P) (F : LFalse P) := 
  falseIntro : False -> (L |- false) 

def falseIntro {L : Logic P} [F : LFalse P]
  [K : FalseIntro L F] := K.falseIntro

class FalseElim (L : Logic P) (F : LFalse P) := 
  falseElim : (L |- false) -> False

def falseElim {L : Logic P} [F : LFalse P]
  [K : FalseElim L F] := K.falseElim

class ExFalso (L : Logic P) (F : LFalse P) :=
  exFalso : (p : P) -> (L |- false) -> (L |- p)

def exFalso {L : Logic P} [F : LFalse P]
  [K : ExFalso L F] {p} := K.exFalso p

end Gaea.Logic