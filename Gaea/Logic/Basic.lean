namespace Gaea

def Logic.{u,v} (prop : Sort u) 
  := prop -> Sort v

namespace Logic

def prop.{u,v} {P : Sort u} (L : Logic.{u,v} P) := P

def Proof.{u,v} {P : Sort u} (L : Logic.{u,v} P) := Sort v

def Judgment.{u,v} {P : Sort u} (L : Logic.{u,v} P) (prop : P) 
  := L prop

end Logic

end Gaea
