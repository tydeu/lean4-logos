universes u v

namespace Gaea.Syntax 

-- Constants

class True (prop : Sort u) :=
  (true : prop)

export True (true)

class False (prop : Sort u) :=
  (false : prop)

export False (false)

-- Connectives

class LIf (prop : Sort u) :=
  (lif : prop -> prop -> prop)

export LIf (lif)

class LIff (prop : Sort u) :=
  (liff : prop -> prop -> prop)

export LIff (liff)

class LAnd (prop : Sort u):=
  (land : prop -> prop -> prop)

export LAnd (land)

class LOr (prop : Sort u) :=
  (lor : prop -> prop -> prop)

export LOr (lor)

-- Equality

class LEq (prop : Sort u) (form : Sort v) :=
  (leq : form -> form -> prop)

export LEq (leq)

-- Quantifiers

class LForall (prop : Sort u) (form : Sort v) :=
  (lForall : (form -> prop) -> prop)

export LForall (lForall)

class LExists (prop : Sort u) (form : Sort v) :=
  (lExists : (form -> prop) -> prop)

export LExists (lExists)

end Gaea.Syntax
