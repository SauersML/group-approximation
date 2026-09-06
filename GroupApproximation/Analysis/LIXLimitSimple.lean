import GroupApproximation.Analysis.LIXLimitAlgebra
import GroupApproximation.Analysis.LIXSimplicityInstance
import GroupApproximation.Analysis.LIXConnectingMapFullnessTower
import GroupApproximation.Meta.AxiomGuard

/-!
# Simplicity of the counterexample algebra, reduced to stage-wise fullness

`cs-simplicity`'s `CStarTower.isSimpleCStar_limit_of_ne_zero` turns fullness of every nonzero
element of every stage into `IsSimpleCStar` of the limit.  It asks for `[PartialOrder T.Limit]`
and `[StarOrderedRing T.Limit]` — instances that carry no information, since a unital C⋆-algebra
has exactly one order making it a `StarOrderedRing`.  They are supplied here, at the
instantiation site, by the repository's standing idiom, so neither `cs-stages` nor `cs-endpoint`
has to carry them.

What remains after this file is one statement in the stages' own vocabulary, with no reference
to the limit at all:

    ∀ (k : ℕ) (a : STW59.StageAlgebra k), a ≠ 0 → ∃ j, k ≤ j ∧ IsFull (lixTower.climb j k a)

`lixTower.climb j k` is the composite connecting map `φ_{k,j}`, and the manuscript's argument for
it is §6: choose `i ≥ k` with `π_{k,i}(x_i)` in the open set where `a` is nonzero; the
point-evaluation summand of `φ_{k,i+1}(a)` is then nonzero in every fibre, and a section nonzero
in every fibre of a bundle of full matrix algebras generates the whole corner.
-/

namespace GroupApproximation

namespace LIX

noncomputable section

attribute [local instance 100000] GroupApproximation.LIX.instSpectralPartialOrder
                                  GroupApproximation.LIX.instSpectralStarOrderedRing

/-- **Simplicity of the counterexample algebra**, reduced to stage-wise fullness of nonzero
elements.  The order instances that `isSimpleCStar_limit_of_ne_zero` needs are discharged here
from `CStarAlgebra.spectralOrder`, so the remaining hypothesis is order-free. -/
theorem lixLimit_isSimpleCStar_of_full
    (hfull : ∀ (k : ℕ) (a : STW59.StageAlgebra k), a ≠ 0 →
      ∃ j, k ≤ j ∧ IsFull (lixTower.climb j k a)) :
    IsSimpleCStar LIXLimit :=
  lixTower.isSimpleCStar_limit_of_ne_zero hfull

/-- **The counterexample algebra is simple.**  Unconditional: the fullness hypothesis is
discharged by `cs-stages`' `STW59.isFull_climb_of_ne_zero`, whose tower argument is matched to
`lixTower` by `lixTower_succHom`, which holds by `rfl`. -/
theorem lixLimit_isSimpleCStar : IsSimpleCStar LIXLimit :=
  lixLimit_isSimpleCStar_of_full fun k a hne =>
    STW59.isFull_climb_of_ne_zero lixTower_succHom k a hne

/-! ### Axiom audit

Simplicity of the counterexample algebra is unconditional, so it takes the stronger gate:
`#audit_closed_axioms` additionally rejects a leading hypothesis, which is what stops a
conditional theorem from passing for an endpoint merely by having a clean closure. -/

#audit_closed_axioms lixLimit_isSimpleCStar

end

end LIX

end GroupApproximation
