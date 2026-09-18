import GroupApproximation.Analysis.QuasidiagonalTrace
import GroupApproximation.Analysis.ShulmanTraceClasses
import GroupApproximation.Meta.AxiomGuard

/-!
# AF algebras with explicit matrix-unit data: vocabulary and the upstream interface

Lane `nm-tww-04` (cartography `lanes/carto-nm-tww.md`): every tracial state on an AF
algebra, given with an explicit presentation, is quasidiagonal.

## What this module fixes

* `Multimatrix r k`, the multimatrix algebra `⊕_{i<r} M_{k_i}(ℂ)`. It carries the
  C⋆-norm (the maximum of the L2 operator norms of the blocks) through the
  non-global instance `multimatrixCStarAlgebra`. Every module of this lane switches it
  on with `attribute [local instance]`.
* `AFPresentation A`: injective unital ⋆-homomorphisms `ιₙ : Bₙ → A` from multimatrix
  algebras, with increasing ranges whose union is dense. This is the standard
  (Bratteli) notion of a unital AF algebra. The field names match
  `SubclassAnswer.MultimatrixAFPresentation` from lane `nm-tww-05`, so the two
  structures convert field by field.
* `MultimatrixTraceAmplificationStatement`: the rational-amplification half of lane
  `nm-tww-03`. That lane is authored in parallel and is not on disk.

## Truth check (the upstream Statement)

Let `τ` be a tracial state on `B = ⊕ M_{k_i}`. It is `∑ tᵢ trᵢ(bᵢ)` with `tᵢ ≥ 0` and
`∑ tᵢ = 1`. For multiplicities `mᵢ` put `N = ∑ mᵢ kᵢ` and `π(b) = ⊕ bᵢ ⊗ 1_{mᵢ}`. This is
a unital ⋆-homomorphism `B → M_N` once `N > 0`, and
`tr_N(π b) = ∑ (mᵢ kᵢ / N) trᵢ(bᵢ)`. The weights `mᵢ kᵢ / N` approximate `(tᵢ)` in `ℓ¹`
arbitrarily well: take a common multiple of the `kᵢ` and a large scale. Also
`|trᵢ(bᵢ)| ≤ ‖bᵢ‖ ≤ ‖b‖`. Together these give `|τ b − tr_N(π b)| ≤ ε‖b‖`. So the
Statement is true, and it is literally the second clause of the `nm-tww-03` lane
(`normTrace` over `Fin N` is `trace / N`).

## Truth check (the lane target)

The target is true. `AFQD/Model.lean` records the route: restrict `τ` to `Bₙ`, amplify,
extend by Arveson, and propagate from the dense union.
-/

namespace GroupApproximation
namespace Manuscript
namespace NonMF
namespace TWWLanes
namespace AFQD

open scoped Matrix.Norms.L2Operator

noncomputable section

/-- **The multimatrix algebra** `⊕_{i<r} M_{k_i}(ℂ)`. -/
abbrev Multimatrix (r : ℕ) (k : Fin r → ℕ) : Type :=
  ∀ i : Fin r, Matrix (Fin (k i)) (Fin (k i)) ℂ

/-- The C⋆-algebra structure on one full matrix block, for the L2 operator norm. This
is not a global instance; switch it on with `attribute [local instance]`. -/
@[reducible]
def matrixBlockCStarAlgebra (m : ℕ) : CStarAlgebra (Matrix (Fin m) (Fin m) ℂ) where
  toNormedRing := inferInstance
  toStarRing := inferInstance
  toCompleteSpace := inferInstance
  toCStarRing := inferInstance
  toNormedAlgebra := inferInstance
  toStarModule := inferInstance

attribute [local instance] matrixBlockCStarAlgebra

/-- The C⋆-algebra structure on a multimatrix algebra: the maximum of the block
norms. This is not a global instance; switch it on with `attribute [local instance]`. -/
@[reducible]
def multimatrixCStarAlgebra (r : ℕ) (k : Fin r → ℕ) :
    CStarAlgebra (Multimatrix r k) where
  toNormedRing := inferInstance
  toStarRing := inferInstance
  toCompleteSpace := inferInstance
  toCStarRing := inferInstance
  toNormedAlgebra := inferInstance
  toStarModule := inferInstance

attribute [local instance] multimatrixCStarAlgebra

/-- **A unital AF presentation** of a C⋆-algebra `A`: injective unital
⋆-homomorphisms `ιₙ : Bₙ → A` from multimatrix algebras, with increasing ranges
whose union is dense. -/
structure AFPresentation (A : Type) [CStarAlgebra A] where
  /-- The number of blocks of the `n`-th multimatrix algebra. -/
  blocks : ℕ → ℕ
  /-- The block sizes of the `n`-th multimatrix algebra. -/
  sizes : ∀ n : ℕ, Fin (blocks n) → ℕ
  /-- The unital ⋆-embeddings `ιₙ : Bₙ → A`. -/
  embed : ∀ n : ℕ, Multimatrix (blocks n) (sizes n) →⋆ₐ[ℂ] A
  /-- Each `ιₙ` is injective. -/
  injective : ∀ n : ℕ, Function.Injective ⇑(embed n)
  /-- The ranges increase. -/
  range_mono : ∀ n : ℕ, Set.range ⇑(embed n) ⊆ Set.range ⇑(embed (n + 1))
  /-- The union of the ranges is dense. -/
  dense : Dense (⋃ n : ℕ, Set.range ⇑(embed n))

/-- **Interface of lane `nm-tww-03`, rational amplification.** A tracial state on a
multimatrix algebra is uniformly approximated, relative to the C⋆-norm, by the
normalized trace of a unital ⋆-representation on some `ℂ^N`.

This is true (see the module docstring). It is exactly the second clause of the
`nm-tww-03` lane, which is not on disk yet. It is not proved here. -/
def MultimatrixTraceAmplificationStatement : Prop :=
  ∀ (r : ℕ) (k : Fin r → ℕ) (τ : TracialState (Multimatrix r k)) (ε : ℝ), 0 < ε →
    ∃ (N : ℕ) (π : Multimatrix r k →⋆ₐ[ℂ] Matrix (Fin N) (Fin N) ℂ),
      ∀ b : Multimatrix r k, ‖τ b - Matrix.trace (π b) / (N : ℂ)‖ ≤ ε * ‖b‖

/-- The range of `ιₘ` lies in the range of `ιₙ` whenever `m ≤ n`. -/
theorem AFPresentation.range_subset {A : Type} [CStarAlgebra A] (P : AFPresentation A)
    {m n : ℕ} (hmn : m ≤ n) : Set.range ⇑(P.embed m) ⊆ Set.range ⇑(P.embed n) :=
  monotone_nat_of_le_succ (f := fun n ↦ Set.range ⇑(P.embed n)) P.range_mono hmn

end

end AFQD
end TWWLanes
end NonMF
end Manuscript
end GroupApproximation

#audit_axioms GroupApproximation.Manuscript.NonMF.TWWLanes.AFQD.Multimatrix
#audit_axioms GroupApproximation.Manuscript.NonMF.TWWLanes.AFQD.matrixBlockCStarAlgebra
#audit_axioms GroupApproximation.Manuscript.NonMF.TWWLanes.AFQD.multimatrixCStarAlgebra
#audit_axioms GroupApproximation.Manuscript.NonMF.TWWLanes.AFQD.AFPresentation
#audit_axioms GroupApproximation.Manuscript.NonMF.TWWLanes.AFQD.MultimatrixTraceAmplificationStatement
#audit_axioms GroupApproximation.Manuscript.NonMF.TWWLanes.AFQD.AFPresentation.range_subset
