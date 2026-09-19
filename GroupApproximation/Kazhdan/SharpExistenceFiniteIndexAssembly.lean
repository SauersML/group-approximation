import GroupApproximation.Algebra.FreeGroupFiniteRank
import GroupApproximation.Kazhdan.LatticeRouteRemainder

/-!
# The finite-index route to the sharp hyperbolic Kazhdan witness

`Kazhdan/LatticeRouteRemainder.lean` predates the unconditional discharge of
its Reidemeister--Schreier input in `Algebra/FreeGroupFiniteRank.lean`.  This
module removes that stale input from the route to
`Hyperbolic.SharpExistence`.

Thus passage to a torsion-free finite-index subgroup already preserves

* property `(T)`, by `FiniteIndex.kazhdanFiniteIndexPermanence`; and
* finite presentation, by
  `FiniteIndex.isFinitelyPresented_subgroup_of_finiteIndex'`.

The abstract finite-index assembly now has one permanence leaf:
`Hyperbolic.QuasiIsometryInvariant`.  Its Morse input is itself a theorem,
`Hyperbolic.morseLemma_univ`, but the general quasi-isometry transport has not
yet been assembled from it.  The other remaining object is an actual
`Hyperbolic.LatticeRouteInput` (for example, an explicit hyperbolic Kazhdan
triangle group together with a torsion-free finite-index kernel).

Nothing in this module assumes either leaf, and no literature statement is
declared as an axiom.
-/

namespace GroupApproximation
namespace FiniteIndex

/-! ## The permanence theorem that was already available -/

/-- **Finite presentation passes to finite-index subgroups**, with no input.

The old wrapper
`finitePresentationFiniteIndexPermanence_of_freeInput` exposed
`FreeFiniteIndexFinitelyPresented`.  That proposition is now the theorem
`freeFiniteIndexFinitelyPresented`, so the wrapper can be closed outright. -/
theorem finitePresentationFiniteIndexPermanence :
    Hyperbolic.FinitePresentationFiniteIndexPermanence := by
  intro Gamma inst Lambda hfinite hfp
  letI := inst
  letI : Lambda.FiniteIndex := hfinite
  exact isFinitelyPresented_subgroup_of_finiteIndex' Lambda hfp

/-! ## Sharp existence with only the live finite-index leaves -/

/-- A hyperbolic Kazhdan lattice with a torsion-free finite-index subgroup
gives `SharpExistence` once hyperbolicity is transported across
quasi-isometries.  Property `(T)` and finite presentation require no inputs. -/
theorem sharpExistence_of_latticeRoute_of_quasiIsometryInvariant
    (hqi : Hyperbolic.QuasiIsometryInvariant)
    (L : Hyperbolic.LatticeRouteInput) : Hyperbolic.SharpExistence :=
  Hyperbolic.sharpExistence_of_latticeRoute
    (hyperbolicFiniteIndexPermanence_of_quasiIsometryInvariant hqi)
    kazhdanFiniteIndexPermanence
    finitePresentationFiniteIndexPermanence L

end FiniteIndex
end GroupApproximation
