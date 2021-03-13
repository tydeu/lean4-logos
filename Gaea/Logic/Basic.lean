namespace Gaea.Logic

def Logic.{u,v} (prop : Sort u) 
  := prop -> Sort v

namespace Logic

def prop.{u,v} {P : Sort u} (L : Logic.{u,v} P) : Sort u 
  := P

def Proof.{u,v} {P : Sort u} (L : Logic.{u,v} P) : Type v 
  := Sort v

def Judgment.{u,v} {P : Sort u} (L : Logic.{u,v} P) (prop : P) : Sort v 
  := L prop

end Logic

export Logic (prop Proof Judgment)

end Gaea.Logic
