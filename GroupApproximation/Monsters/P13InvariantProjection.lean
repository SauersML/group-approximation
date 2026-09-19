import GroupApproximation.Kazhdan.KazhdanFixedSpace
import GroupApproximation.Monsters.P13SpectralGapNorm

/-!
# Step 1's projection estimate: an almost-fixed vector is near an invariant one

Manuscript: `non_mf_groups_exist.tex`, Proposition `\ref{prop:literal-base-T}`
(subsection *Property (T) of the base*), **Step 1**.  The two sentences
formalized here were the last two of that step:

> "Hence a unit vector almost fixed by the six generators has small Laplacian
> energy and is close to an invariant vector."
>
> "This yields a Kazhdan pair: `P₁₃` has property (T)."

**Neither is printed any more.**  Commit `3a45fa60` ("Editorial pass: rewrite
orbit collapse, cut what nothing uses") replaced the whole three-step
property-`(T)` proof with a one-paragraph citation of
`\ref{rem:classical-base}` and `\cite[Example~1.7.4(i)]{BHV}`.  The proposition
and its badge are unchanged; the quotations above are a record of the deleted
text, kept so the rows of `notes/P13_STEP_AUDIT.md` stay readable, and nothing
below is badgeable on their account.

## What was missing

`Monsters/P13SpectralGap.lean` proves the printed spectral localization and the
printed identification `ker Δ = invariants`; `Monsters/P13SpectralGapNorm.lean`
turns them into the printed lower bound `‖Δx‖ ≥ (1/500)‖x‖` in a representation
without invariant vectors.  What no declaration stated is the *conclusion* those
sentences are drawn towards: the projection/distance estimate.  The existing
route to a Kazhdan pair (`ExactHodgeCertificate.Certificate.isKazhdanPair`)
argues dually — it assumes `hno` outright and produces a moved generator — so it
never exhibits a nearby invariant vector, and it reaches property `(T)` at a
constant several orders of magnitude below what the printed gap supports.

## What is proved here

`t1_06_norm_sub_fixedProjection_le` is the printed distance statement: writing
`P` for the orthogonal projection onto the invariants (equivalently, by
`coe_fixedSubspace_top_eq_ker`, onto `ker Δ`),

  `‖v - P v‖ ≤ 1000 · ∑ᵢ ‖ρ(sᵢ)v - v‖`

for every vector `v` of every orthogonal representation of `P₁₃` on a complete
real inner product space.  The constant is the printed one: `1000 = 2 · 500` is
exactly the printed gap `1/500` composed with `‖Δv‖ ≤ 2∑ᵢ‖ρ(sᵢ)v - v‖`.

The argument is the printed one.  Split `v = P v + m` orthogonally.  `Δ` kills
`P v`, so `Δ m = Δ v`; the moving part `m` lies in the orthogonal complement of
the invariants, on which the subrepresentation has no nonzero invariant vector,
so the printed lower bound applies there and gives `(1/500)‖m‖ ≤ ‖Δ m‖`.  The
only technical ingredient is that the Laplacian of the moving subrepresentation
is the ambient Laplacian restricted, which is `coe_generatorLaplacian_movingRepresentation`.

`t1_07_p13_isKazhdanPair` then reads the Kazhdan pair straight off the distance
estimate, as printed: at tolerance `1/12000` the six displacements sum to at
most `1/2000`, so a unit vector is within `1/2` of its invariant projection and
that projection is nonzero.  This is the declaration the property-`(T)` bridge
of `Sofic/LiteralBaseP13PropertyTBridge.lean` consumes, so the badged endpoint
now travels the printed route rather than the Richardson iteration.
-/

namespace GroupApproximation
namespace P13InvariantProjection

open ExactHodgeCertificate LiteralP13Presentation KazhdanFixedSpace

universe u v

/-! ## The Laplacian of the moving subrepresentation -/

section Abstract

variable {G : Type u} [Group G]
variable {E : Type v} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- **The Laplacian commutes with the fixed/moving splitting.**  The generator
Laplacian of the subrepresentation carried by the moving subspace is the ambient
generator Laplacian, computed on the underlying vector.

This is what licenses transporting the printed lower bound `‖Δx‖ ≥ (1/500)‖x‖`,
which is proved in a representation *without* invariant vectors, to the moving
part of a representation that has them.  Both Laplacians are the same finite sum
of the same group elements acting through the same isometries, so the identity
is a term-by-term comparison. -/
theorem coe_generatorLaplacian_movingRepresentation
    {I : Type*} [Fintype I] (s : I → G) (rho : G →* (E ≃ₗᵢ[ℝ] E))
    (y : movingSubspace rho) :
    ((generatorLaplacianOperator s (movingRepresentation rho) y :
        movingSubspace rho) : E)
      = generatorLaplacianOperator s rho (y : E) := by
  simp only [generatorLaplacianOperator_apply, Submodule.coe_sum,
    Submodule.coe_sub, movingRepresentation_apply]

/-- A vector fixed by the whole group is annihilated by the generator
Laplacian: every summand `ρ(sᵢ)⁻¹(ρ(sᵢ)y - y) - (ρ(sᵢ)y - y)` vanishes on the
nose.  This is the direction of `P13SpectralGap.ker_generatorLaplacian_eq_invariants`
that the distance estimate consumes, in the pointwise form. -/
theorem generatorLaplacian_eq_zero_of_invariant
    {I : Type*} [Fintype I] (s : I → G) (rho : G →* (E ≃ₗᵢ[ℝ] E)) {y : E}
    (hy : ∀ g : G, rho g y = y) :
    generatorLaplacianOperator s rho y = 0 := by
  rw [generatorLaplacianOperator_apply]
  refine Finset.sum_eq_zero fun i _ ↦ ?_
  rw [hy (s i)]
  simp

end Abstract

/-! ## The printed distance estimate for `P₁₃` -/

section P13

variable {E : Type v} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- The subspace the projection of Step 1 is taken onto is literally the kernel
of `Δ`, by the printed identification `ker Δ = invariants`
(`P13SpectralGap.t1_05_p13_ker_eq_invariants`).  So "the projection onto
`ker Δ`" and "the projection onto the invariants" name the same operator, and
the estimate below may be read either way. -/
theorem coe_fixedSubspace_top_eq_ker (rho : P13 →* (E ≃ₗᵢ[ℝ] E)) :
    (fixedSubspace rho ⊤ : Set E)
      = {y : E | generatorLaplacianOperator p13Generator rho y = 0} := by
  rw [P13SpectralGap.t1_05_p13_ker_eq_invariants rho]
  ext y
  simp

/-- **Step 1, "small Laplacian energy", exactly.**  The Laplacian energy of a
vector is the sum of the squared generator displacements, so it is small
precisely when the vector is almost fixed by the six generators. -/
theorem t1_06_energy_eq (rho : P13 →* (E ≃ₗᵢ[ℝ] E)) (y : E) :
    PositiveOperatorGap.energy (generatorLaplacianOperator p13Generator rho) y
      = ∑ i, ‖rho (p13Generator i) y - y‖ ^ 2 :=
  generatorLaplacian_energy p13Generator rho y

/-- **Step 1, "small Laplacian energy", quantitatively.**  A vector displaced by
at most `eps` by each of the six generators has Laplacian energy at most
`6·eps²`. -/
theorem t1_06_energy_le (rho : P13 →* (E ≃ₗᵢ[ℝ] E)) (y : E) {eps : ℝ}
    (hnear : ∀ i, ‖rho (p13Generator i) y - y‖ ≤ eps) :
    PositiveOperatorGap.energy (generatorLaplacianOperator p13Generator rho) y
      ≤ 6 * eps ^ 2 := by
  rw [t1_06_energy_eq]
  calc
    ∑ i, ‖rho (p13Generator i) y - y‖ ^ 2 ≤ ∑ _i : Fin 6, eps ^ 2 :=
      Finset.sum_le_sum fun i _ ↦
        pow_le_pow_left₀ (norm_nonneg _) (hnear i) 2
    _ = 6 * eps ^ 2 := by
      rw [Finset.sum_const, Finset.card_fin, nsmul_eq_mul]
      norm_num

/-- **The printed lower bound, on the orthogonal complement of the invariants.**
A vector orthogonal to every invariant vector satisfies `(1/500)‖z‖ ≤ ‖Δz‖`.

The moving subrepresentation has, by construction, no nonzero invariant vector
(`KazhdanFixedSpace.movingRepresentation_hasNoInvariantVectors`), which is
exactly the hypothesis under which `P13SpectralGapNorm.p13_norm_lower_bound`
delivers the printed constant; `coe_generatorLaplacian_movingRepresentation`
reads the resulting inequality back in the ambient space. -/
theorem norm_lower_bound_of_mem_movingSubspace [CompleteSpace E]
    (rho : P13 →* (E ≃ₗᵢ[ℝ] E)) {z : E} (hz : z ∈ movingSubspace rho) :
    (1 / 500 : ℝ) * ‖z‖
      ≤ ‖generatorLaplacianOperator p13Generator rho z‖ := by
  haveI : CompleteSpace (movingSubspace rho) :=
    (Submodule.isClosed_orthogonal (fixedSubspace rho ⊤)).completeSpace_coe
  have h := P13SpectralGapNorm.p13_norm_lower_bound (movingRepresentation rho)
    (movingRepresentation_hasNoInvariantVectors rho) ⟨z, hz⟩
  -- The norm of a submodule element is the ambient norm of its underlying
  -- vector, definitionally (`Submodule.coe_norm`), so `h` may be read at once
  -- in the ambient space.
  have h' : (1 / 500 : ℝ) * ‖z‖
      ≤ ‖((generatorLaplacianOperator p13Generator (movingRepresentation rho)
          ⟨z, hz⟩ : movingSubspace rho) : E)‖ := h
  rw [coe_generatorLaplacian_movingRepresentation] at h'
  exact h'

/-- **Manuscript Step 1, item T1.06**: *"a unit vector almost fixed by the six
generators … is close to an invariant vector."*

`P = fixedProjection ρ ⊤` is the orthogonal projection onto the space of
invariant vectors — equivalently, by `coe_fixedSubspace_top_eq_ker`, onto
`ker Δ`.  The estimate

  `‖v - P v‖ ≤ 1000 · ∑ᵢ ‖ρ(sᵢ)v - v‖`

carries the printed constant: `1000 = 2·500`, the printed spectral gap `1/500`
composed with the universal comparison `‖Δv‖ ≤ 2∑ᵢ‖ρ(sᵢ)v - v‖`.

The proof is the printed argument.  `Δ` annihilates `P v`, so `Δ(v - P v) = Δv`;
the residual `v - P v` is orthogonal to the invariants, where the printed lower
bound holds with no loss. -/
theorem t1_06_norm_sub_fixedProjection_le [CompleteSpace E]
    (rho : P13 →* (E ≃ₗᵢ[ℝ] E)) (y : E) :
    ‖y - (fixedProjection rho ⊤ y : E)‖
      ≤ 1000 * ∑ i, ‖rho (p13Generator i) y - y‖ := by
  have hmsub : subgroupMovingProjection rho ⊤ y
      = y - (fixedProjection rho ⊤ y : E) :=
    subgroupMovingProjection_eq_sub_fixedProjection rho ⊤ y
  have hmem : y - (fixedProjection rho ⊤ y : E) ∈ movingSubspace rho := by
    rw [← hmsub]
    exact subgroupMovingProjection_mem rho ⊤ y
  have hfix : ∀ g : P13, rho g (fixedProjection rho ⊤ y : E)
      = (fixedProjection rho ⊤ y : E) :=
    fun g ↦ fixedProjection_mem rho ⊤ y ⟨g, Subgroup.mem_top g⟩
  have hlap : generatorLaplacianOperator p13Generator rho
        (y - (fixedProjection rho ⊤ y : E))
      = generatorLaplacianOperator p13Generator rho y := by
    rw [map_sub, generatorLaplacian_eq_zero_of_invariant p13Generator rho hfix,
      sub_zero]
  have hlow := norm_lower_bound_of_mem_movingSubspace rho hmem
  rw [hlap] at hlow
  have htwo := norm_generatorLaplacian_le_two_sum p13Generator rho y
  linarith

/-- **Manuscript Step 1, item T1.07**: *"This yields a Kazhdan pair: `P₁₃` has
property (T)."*

The pair is read straight off the distance estimate, as printed: the six
generators are the control set, and at tolerance `1/12000` the six displacements
of a unit vector sum to at most `1/2000`, so the invariant projection is within
`1/2` of it and in particular nonzero.

Nothing here re-derives the certificate: the only analytic input is
`t1_06_norm_sub_fixedProjection_le`, hence the printed spectral gap `1/500`. -/
theorem t1_07_p13_isKazhdanPair :
    IsKazhdanPair.{0, v} P13 (generatorFinset p13Generator) (1 / 12000) := by
  refine ⟨by norm_num, ?_⟩
  intro E _ _ _ rho y hy hnear
  refine ⟨(fixedProjection rho ⊤ y : E), ?_,
    fun g ↦ fixedProjection_mem rho ⊤ y ⟨g, Subgroup.mem_top g⟩⟩
  have hsum : ∑ i, ‖rho (p13Generator i) y - y‖ ≤ (1 / 2000 : ℝ) := by
    calc
      ∑ i, ‖rho (p13Generator i) y - y‖ ≤ ∑ _i : Fin 6, (1 / 12000 : ℝ) :=
        Finset.sum_le_sum fun i _ ↦
          (hnear (p13Generator i) (by simp [generatorFinset])).le
      _ = 1 / 2000 := by
        rw [Finset.sum_const, Finset.card_fin, nsmul_eq_mul]
        norm_num
  have hdist := t1_06_norm_sub_fixedProjection_le rho y
  intro hzero
  rw [hzero, sub_zero] at hdist
  linarith

/-- **Step 1's endpoint, by the printed route.**  `P₁₃` has property `(T)`,
proved through the spectral localization, the identification of `ker Δ` with the
invariants, the printed lower bound, and the projection estimate — the four
sentences the manuscript prints, in that order.

This is the declaration `Sofic/LiteralBaseP13PropertyTBridge.lean` feeds to the
Step 2 quotient transfer; `LiteralP13HodgeCertificate.p13_hasKazhdanPropertyT`
remains available as the alternate Richardson route. -/
theorem t1_07_p13_hasKazhdanPropertyT : HasKazhdanPropertyT.{0, v} P13 :=
  ⟨generatorFinset p13Generator, 1 / 12000, t1_07_p13_isKazhdanPair⟩

end P13

end P13InvariantProjection
end GroupApproximation
