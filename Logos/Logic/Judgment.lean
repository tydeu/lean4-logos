import Logos.Logic.Logic

universes u v
variable {P : Sort u}

namespace Logos

def Judgment (L : Logic.{u,v} P) (prop : P) : Sort v :=
  L.judge prop

def NoJudgment (L : Logic.{u,v} P) (prop : P) :=
  L.judge prop -> False

scoped infix:15 " |- " => Judgment
scoped infix:15 " ⊢ " => Judgment

scoped infix:15 " !|- " => NoJudgment
scoped infix:15 " ⊬ " => NoJudgment

namespace Logic

abbrev Prod (L : Logic.{u,v} P) (p q : P) : Sort (max 1 v)
  := PProd (L |- p) (L |- q) 

abbrev prod (L : Logic.{u,v} P) {p q : P} 
  (Lp : L |- p) (Lq : L |- q) : L.Prod p q
  := PProd.mk Lp Lq 

abbrev Sum (L : Logic.{u,v} P) (p q : P)  : Sort (max 1 v)
  := PSum (L |- p) (L |- q)

abbrev suml (L : Logic.{u,v} P) {p q : P} (Lp : L |- p) : L.Sum p q
  := PSum.inl Lp 

abbrev sumr (L : Logic.{u,v} P) {p q : P} (Lq : L |- q) : L.Sum p q
  := PSum.inr Lq 
