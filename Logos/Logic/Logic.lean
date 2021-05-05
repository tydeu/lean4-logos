namespace Logos

universes u v

class Logic (P : Sort u) :=
  judge : P -> Sort v

namespace Logic

variable {P : Sort u}

abbrev «Prop» (L : Logic.{u,v} P) : Sort u 
  := P

abbrev Proof (L : Logic.{u,v} P) : Type v 
  := Sort v
