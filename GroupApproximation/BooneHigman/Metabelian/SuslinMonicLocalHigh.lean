import GroupApproximation.BooneHigman.Metabelian.SuslinMonicLocalEndpoint
import GroupApproximation.BooneHigman.Metabelian.SuslinMonicStabReduce
import GroupApproximation.Meta.AxiomGuard

/-!
# The high-degree monic Statement of lane `bh-met-93h` over a local ring

Lane `bh-met-93i`.  `suslinMonic_StabHigh R` (`SuslinMonicStabReduce.lean`) holds for every
commutative local ring `R`: it is a special case of `suslinMonicLocal_monicStab`.
-/

namespace GroupApproximation
namespace BooneHigman
namespace Metabelian
namespace Absorption

/-- **`suslinMonic_StabHigh` over a local ring**, unconditionally. -/
theorem suslinMonicLocal_stabHigh (R : Type*) [CommRing R] [IsLocalRing R] :
    suslinMonic_StabHigh R := by
  intro τ hdet hlc _ _ hc
  exact suslinMonicLocal_monicStab R τ hdet hlc hc

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Absorption.suslinMonicLocal_stabHigh

end Absorption
end Metabelian
end BooneHigman
end GroupApproximation
