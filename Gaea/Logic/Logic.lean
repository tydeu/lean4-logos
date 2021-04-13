namespace Gaea

class Logic.{u,v} (P : Sort u) :=
  judgment : P -> Sort v

namespace Logic

def prop.{u,v} {P : Sort u} (L : Logic.{u,v} P) : Sort u 
  := P

def proof.{u,v} {P : Sort u} (L : Logic.{u,v} P) : Type v 
  := Sort v

end Logic

end Gaea
