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


namespace Gen

/-- **Simplicity of the counterexample algebra at rank `n`**, reduced to stage-wise fullness
of nonzero elements.  The order instances that `isSimpleCStar_limit_of_ne_zero` needs are
discharged here from `CStarAlgebra.spectralOrder`, so the remaining hypothesis is order-free. -/
theorem lixLimit_isSimpleCStar_of_full (n : ℕ) [NeZero n]
    (hfull : ∀ (k : ℕ) (a : STW59.Gen.StageAlgebra n k), a ≠ 0 →
      ∃ j, k ≤ j ∧ IsFull ((lixTower n).climb j k a)) :
    IsSimpleCStar (LIXLimit n) :=
  (lixTower n).isSimpleCStar_limit_of_ne_zero hfull

/-- **The counterexample algebra at rank `n` is simple.**  Unconditional: the fullness
hypothesis is discharged by `STW59.Gen.isFull_climb_of_ne_zero`, whose tower argument is
matched to `Gen.lixTower n` by `Gen.lixTower_succHom`, which holds by `rfl`. -/
theorem lixLimit_isSimpleCStar (n : ℕ) [NeZero n] : IsSimpleCStar (LIXLimit n) :=
  lixLimit_isSimpleCStar_of_full n fun k a hne =>
    STW59.Gen.isFull_climb_of_ne_zero n (lixTower_succHom n) k a hne

end Gen

/-! ### The `n = 2` instance -/

/-- **Simplicity of the counterexample algebra**, reduced to stage-wise fullness of nonzero
elements. -/
theorem lixLimit_isSimpleCStar_of_full
    (hfull : ∀ (k : ℕ) (a : STW59.StageAlgebra k), a ≠ 0 →
      ∃ j, k ≤ j ∧ IsFull (lixTower.climb j k a)) :
    IsSimpleCStar LIXLimit :=
  Gen.lixLimit_isSimpleCStar_of_full 2 hfull

/-- **The counterexample algebra is simple.** -/
theorem lixLimit_isSimpleCStar : IsSimpleCStar LIXLimit := Gen.lixLimit_isSimpleCStar 2

/-! ### Axiom audit

Simplicity of the counterexample algebra is unconditional, so it takes the stronger gate:
`#audit_closed_axioms` additionally rejects a leading hypothesis, which is what stops a
conditional theorem from passing for an endpoint merely by having a clean closure. -/

#audit_closed_axioms lixLimit_isSimpleCStar

/-! The generic theorem takes the rank as a leading input, so it gets the plain audit:
`#audit_closed_axioms` rejects any leading argument by design, and that rejection is the
gate doing its job, not a defect to work around.  The `n = 2` instance above is the closed
proposition and keeps the stronger gate. -/

#audit_axioms Gen.lixLimit_isSimpleCStar

end

end LIX

end GroupApproximation
