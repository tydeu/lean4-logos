universes u v

namespace Gaea.Syntax 

-- Constants

class LTrue (prop : Sort u) :=
  (lTrue : prop)

class LFalse (prop : Sort u) :=
  (lFalse : prop)

-- Connectives

class LIf (prop : Sort u) :=
  (lIf : prop -> prop -> prop)

class LIff (prop : Sort u) :=
  (lIff : prop -> prop -> prop)

class LAnd (prop : Sort u):=
  (lAnd : prop -> prop -> prop)

class LOr (prop : Sort u) :=
  (lOr : prop -> prop -> prop)

class LNot (prop : Sort u) :=
  (lNot : prop -> prop)

-- Equality

class LEq (prop : Sort u) (form : Sort v) :=
  (lEq : form -> form -> prop)

-- Quantifiers

class LForall (prop : Sort u) (form : Sort v) :=
  (lForall : (form -> prop) -> prop)

class LExists (prop : Sort u) (form : Sort v) :=
  (lExists : (form -> prop) -> prop)

end Gaea.Syntax