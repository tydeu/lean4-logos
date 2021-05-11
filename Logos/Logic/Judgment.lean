import Logos.Logic.Logic
import Logos.Prelude.Newtype

universe u
variable {P : Sort u}

namespace Logos

class newtype Judgment (L : Logic P) (p : P) :=
  proof : L.judge p

scoped infix:15 " |- " => Judgment
scoped infix:15 " ⊢ " => Judgment

class funtype NoJudgment (L : Logic P) (p : P) :=
  proof : (L |- p) -> False

scoped infix:15 " !|- " => NoJudgment
scoped infix:15 " ⊬ " => NoJudgment

abbrev noJudgment {L : Logic P} {p : P} 
  : ((L |- p) -> False) -> (L !|- p) 
  := NoJudgment.mk

namespace Logic

abbrev Prod (L : Logic P) (p q : P)
  := _root_.Prod (L |- p) (L |- q) 

abbrev prod (L : Logic P) {p q : P} 
  (Lp : L |- p) (Lq : L |- q) : L.Prod p q
  := Prod.mk Lp Lq 

abbrev Sum (L : Logic P) (p q : P)
  := _root_.Sum (L |- p) (L |- q)

abbrev suml (L : Logic P) {p q : P} (Lp : L |- p) : L.Sum p q
  := Sum.inl Lp 

abbrev sumr (L : Logic P) {p q : P} (Lq : L |- q) : L.Sum p q
  := Sum.inr Lq 
