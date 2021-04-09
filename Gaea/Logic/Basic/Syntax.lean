universes u v

namespace Gaea.Logic 

-- Constants

class LTrue (prop : Sort u) :=
  (lTrue : prop)

class LFalse (prop : Sort u) :=
  (lFalse : prop)

-- Connectives

class Imp (prop : Sort u) :=
  (imp : prop -> prop -> prop)

class LIff (prop : Sort u) :=
  (lIff : prop -> prop -> prop)

class Conj (prop : Sort u):=
  (conj : prop -> prop -> prop)

class Disj (prop : Sort u) :=
  (disj : prop -> prop -> prop)

class LNot (prop : Sort u) :=
  (lNot : prop -> prop)

-- Quantifiers

class LForall (prop : Sort u) (form : Sort v) :=
  (lForall : (form -> prop) -> prop)

class LExists (prop : Sort u) (form : Sort v) :=
  (lExists : (form -> prop) -> prop)

end Gaea.Logic