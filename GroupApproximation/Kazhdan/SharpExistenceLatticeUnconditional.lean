import GroupApproximation.Algebra.HyperbolicQuasiIsometryInvariant
import GroupApproximation.Kazhdan.SharpExistenceFiniteIndexAssembly

/-!
# The lattice route with all permanence theorems discharged

The Morse lemma is now assembled into quasi-isometry invariance in
`Algebra/HyperbolicQuasiIsometryInvariant.lean`.  Consequently hyperbolicity,
finite presentation, and property `(T)` all pass to the torsion-free
finite-index subgroup in `Hyperbolic.LatticeRouteInput` without additional
inputs.  The only residual in this route is the concrete lattice datum itself.
-/

namespace GroupApproximation
namespace FiniteIndex

/-- **Hyperbolicity passes to finite-index subgroups, unconditionally.** -/
theorem hyperbolicFiniteIndexPermanence :
    Hyperbolic.HyperbolicFiniteIndexPermanence :=
  hyperbolicFiniteIndexPermanence_of_quasiIsometryInvariant
    Hyperbolic.quasiIsometryInvariant

/-- **The sharp Kazhdan witness from one concrete lattice datum.**

There are no permanence or literature-theorem binders left: property `(T)`,
finite presentation, and hyperbolicity are transported by theorems. -/
theorem sharpExistence_of_latticeRoute_unconditional
    (L : Hyperbolic.LatticeRouteInput) : Hyperbolic.SharpExistence :=
  sharpExistence_of_latticeRoute_of_quasiIsometryInvariant
    Hyperbolic.quasiIsometryInvariant L

end FiniteIndex
end GroupApproximation
