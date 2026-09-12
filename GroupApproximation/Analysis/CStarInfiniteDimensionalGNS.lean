import GroupApproximation.Analysis.CStarSeparableFaithfulRepresentation

/-!
# The GNS sum is infinite-dimensional

`ShulmanFill.UnitalTailPairPackageStatement` asks its Hilbert space to be
infinite-dimensional, because `not_theorem4PrintedPair` shows the printed models
cannot be placed on a finite-dimensional one at all.  The space
`CStarState.exists_typeZero_faithful_representation` produces is an isometric
copy of `FamilyGNSSpace ψ`, and this module shows that space has the clause.

The reason is the obvious one and needs no property of the states beyond the one
already proved: `lp.single 2 n Ω_n`, for `Ω_n` the cyclic vector of the `n`-th
state, is an orthonormal family indexed by `ℕ` --- distinct coordinates are
orthogonal because the singles are, and each has norm one because
`State.norm_gnsVector` says the cyclic vector does.  An orthonormal family
indexed by an infinite type is linearly independent, so the rank is at least
`ℵ₀`, so the space is not finite-dimensional.

The first lemma is stated for an arbitrary inner product space, since nothing
about GNS enters it.
-/

namespace GroupApproximation
namespace CStarState

open Filter Topology

open scoped InnerProductSpace

noncomputable section

universe u

/-- **A space carrying an orthonormal sequence is not finite-dimensional.**
Orthonormal families are linearly independent, and a linearly independent family
indexed by `ℕ` forces the rank to be at least `ℵ₀`. -/
theorem not_finiteDimensional_of_orthonormal_nat {E : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℂ E] {v : ℕ → E}
    (hv : Orthonormal ℂ v) : ¬ FiniteDimensional ℂ E := by
  intro hfd
  have hle : Cardinal.aleph0 ≤ Module.rank ℂ E :=
    hv.linearIndependent.aleph0_le_rank
  have hlt : Module.rank ℂ E < Cardinal.aleph0 :=
    Module.rank_lt_aleph0_iff.mpr hfd
  exact absurd hlt (not_lt.mpr hle)

variable {A : Type u} [CStarAlgebra A] [Nontrivial A]

/-- **The cyclic vectors, placed on distinct coordinates, are orthonormal.** -/
theorem orthonormal_single_gnsVector (ψ : ℕ → State A) :
    Orthonormal ℂ (fun n : ℕ ↦
      lp.single 2 n (ψ n).gnsVector : ℕ → FamilyGNSSpace ψ) := by
  classical
  constructor
  · intro n
    rw [lp.norm_single, (ψ n).norm_gnsVector]
    norm_num
  · intro i j hij
    rw [lp.inner_single_left, lp.single_apply, Pi.single_eq_of_ne hij,
      inner_zero_right]

/-- **The GNS sum of a sequence of states is infinite-dimensional.** -/
theorem not_finiteDimensional_familyGNSSpace (ψ : ℕ → State A) :
    ¬ FiniteDimensional ℂ (FamilyGNSSpace ψ) :=
  not_finiteDimensional_of_orthonormal_nat (orthonormal_single_gnsVector ψ)

end

end CStarState
end GroupApproximation
