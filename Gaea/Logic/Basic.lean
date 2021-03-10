universes u v w

namespace Gaea

structure Logic :=
  (prop : Sort u)
  (proof : prop -> Sort v)

end Gaea
