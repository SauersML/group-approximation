import GroupApproximation.Sofic.CollapseJointCorner

/-!
# Refining a corner partition: the joint corner of a commuting family

`Sofic/CollapseJointCorner.lean` compresses along the joint corner structure of
a finite commuting family of exact involutions by composing the block averages
of the individual two-block cuts.  This file justifies calling that composite a
*block compression along the joint corner structure*, in the sense of Step 1 of
the proof sketch of `\ref{thm:collapse}` that `non_mf_groups_exist.tex` used to
print (`block compression along the finite commutative corner structure`).  That
sketch was replaced in commit `3a45fa60`; see the header of
`Sofic/CollapseJointCorner.lean` for what the manuscript prints instead.

The content is one lemma.  If `A` and `P` are corner partitions — finite
families of pairwise orthogonal projections summing to `1` — whose members
commute with each other, then the products `A a * P k` form a corner partition
indexed by `α × κ` (the common refinement), and compression along the
refinement is the composition of the two compressions:

`cornerCompression (cornerRefine A P) = cornerCompression A ∘ cornerCompression P`.

Iterating this over a family `R i`, `i ∈ l`, of commuting exact involutions,
starting from the two-block cuts `involutionCut (R i)`, exhibits
`CollapseJointCorner.jointCompression R l` as the corner compression along a
corner partition with `2 ^ l.length` blocks: the joint spectral blocks of the
family, which is exactly the "finite commutative corner structure of the
previously corrected microstates" of the manuscript.  The two-involution case
is spelled out at the end.

Note what this means for the cost.  `ExactInvolutionLifts.
norm_cornerInvolutionCorrection_sub_le` is linear in the number of *blocks*,
and the joint corner of `m` involutions has `2 ^ m` blocks, so quoting that
lemma at full block count would give a bound of order `m * 2 ^ m * η` — better
than the iterated route's `15 ^ m * η`, but still exponential.  The bound
`3/2 * m * η` of `CollapseJointCorner.norm_jointInvolutionCorrection_sub_le` is
obtained instead by estimating the *same* compression through the composition
above: each factor is a contraction that moves `v` by at most `η / 2`, so the
`m` errors add rather than multiply.
-/

namespace GroupApproximation
namespace CollapseJointCorner

open Matrix
open KazhdanCornerMatrices
open ExactInvolutionLifts
open scoped Matrix.Norms.L2Operator

variable {Y : Type*} [Fintype Y] [DecidableEq Y]

section Refinement

variable {α κ : Type*} [Fintype α] [Fintype κ]

/-- The common refinement of two corner partitions: the family of products,
indexed by the product of the index types. -/
def cornerRefine (A : α → Matrix Y Y ℂ) (P : κ → Matrix Y Y ℂ) (p : α × κ) :
    Matrix Y Y ℂ :=
  A p.1 * P p.2

omit [Fintype α] [Fintype κ] [DecidableEq Y] in
/-- Each block of the refinement is an orthogonal projection: a product of two
commuting orthogonal projections. -/
theorem cornerRefine_isOrthogonalProjectionMatrix (A : α → Matrix Y Y ℂ)
    (P : κ → Matrix Y Y ℂ)
    (hA : ∀ a, IsOrthogonalProjectionMatrix (A a))
    (hP : ∀ k, IsOrthogonalProjectionMatrix (P k))
    (hAP : ∀ a k, A a * P k = P k * A a) (p : α × κ) :
    IsOrthogonalProjectionMatrix (cornerRefine A P p) := by
  constructor
  · rw [cornerRefine, Matrix.conjTranspose_mul, (hP p.2).1, (hA p.1).1,
      ← hAP p.1 p.2]
  · rw [cornerRefine]
    calc (A p.1 * P p.2) * (A p.1 * P p.2)
        = A p.1 * (P p.2 * A p.1) * P p.2 := by noncomm_ring
      _ = A p.1 * (A p.1 * P p.2) * P p.2 := by rw [hAP p.1 p.2]
      _ = (A p.1 * A p.1) * (P p.2 * P p.2) := by noncomm_ring
      _ = A p.1 * P p.2 := by rw [(hA p.1).2, (hP p.2).2]

omit [Fintype α] [Fintype κ] in
/-- Distinct blocks of the refinement are orthogonal: they differ in at least
one coordinate, and the corresponding factors annihilate each other. -/
theorem cornerRefine_orthogonal (A : α → Matrix Y Y ℂ) (P : κ → Matrix Y Y ℂ)
    (hAorth : ∀ a a', a ≠ a' → A a * A a' = 0)
    (hPorth : ∀ k k', k ≠ k' → P k * P k' = 0)
    (hAP : ∀ a k, A a * P k = P k * A a) :
    ∀ p q : α × κ, p ≠ q → cornerRefine A P p * cornerRefine A P q = 0 := by
  rintro ⟨a, k⟩ ⟨a', k'⟩ hpq
  show (A a * P k) * (A a' * P k') = 0
  have hswap : (A a * P k) * (A a' * P k') = (A a * A a') * (P k * P k') := by
    calc (A a * P k) * (A a' * P k')
        = A a * (P k * A a') * P k' := by noncomm_ring
      _ = A a * (A a' * P k) * P k' := by rw [← hAP a' k]
      _ = (A a * A a') * (P k * P k') := by noncomm_ring
  rw [hswap]
  by_cases h1 : a = a'
  · have h2 : k ≠ k' := by
      intro hk
      exact hpq (by rw [h1, hk])
    rw [hPorth k k' h2]
    simp
  · rw [hAorth a a' h1]
    simp

/-- The refinement of two corner partitions is again a partition of the
identity. -/
theorem cornerRefine_sum (A : α → Matrix Y Y ℂ) (P : κ → Matrix Y Y ℂ)
    (hAsum : ∑ a, A a = 1) (hPsum : ∑ k, P k = 1) :
    ∑ p : α × κ, cornerRefine A P p = 1 := by
  have hstep : ∑ p : α × κ, cornerRefine A P p = ∑ a : α, ∑ k : κ, A a * P k := by
    rw [Fintype.sum_prod_type]
    simp only [cornerRefine]
  rw [hstep]
  calc ∑ a : α, ∑ k : κ, A a * P k = ∑ a : α, A a * ∑ k : κ, P k := by
        refine Finset.sum_congr rfl fun a _ ↦ ?_
        rw [Finset.mul_sum]
    _ = ∑ a : α, A a := by
        rw [hPsum]
        simp only [Matrix.mul_one]
    _ = 1 := hAsum

omit [DecidableEq Y] in
/-- **Compression along a refinement is a composition of compressions.**  This
is what licenses reading a composite of two-block compressions as a single
block compression along the joint corner structure. -/
theorem cornerCompression_cornerRefine (A : α → Matrix Y Y ℂ)
    (P : κ → Matrix Y Y ℂ) (hAP : ∀ a k, A a * P k = P k * A a)
    (x : Matrix Y Y ℂ) :
    cornerCompression (cornerRefine A P) x
      = cornerCompression A (cornerCompression P x) := by
  have hinner : ∀ a : α, ∑ k : κ, (A a * P k) * x * (A a * P k)
      = A a * cornerCompression P x * A a := by
    intro a
    rw [cornerCompression, Finset.mul_sum, Finset.sum_mul]
    refine Finset.sum_congr rfl fun k _ ↦ ?_
    calc (A a * P k) * x * (A a * P k)
        = A a * (P k * x * (A a * P k)) := by noncomm_ring
      _ = A a * (P k * x * (P k * A a)) := by rw [hAP a k]
      _ = A a * (P k * x * P k) * A a := by noncomm_ring
  have hstep : cornerCompression (cornerRefine A P) x
      = ∑ a : α, ∑ k : κ, (A a * P k) * x * (A a * P k) := by
    rw [cornerCompression, Fintype.sum_prod_type]
    simp only [cornerRefine]
  rw [hstep, cornerCompression]
  exact Finset.sum_congr rfl fun a _ ↦ hinner a

end Refinement

/-! ## The joint corner of two commuting exact involutions

The four joint spectral blocks of a commuting pair, and the identification of
the composite of the two block averages with the compression along them. -/

/-- Two commuting exact involutions have commuting spectral cuts. -/
theorem involutionCut_commute {R₁ R₂ : Matrix Y Y ℂ} (hcomm : R₁ * R₂ = R₂ * R₁)
    (b c : Bool) :
    involutionCut R₁ b * involutionCut R₂ c =
      involutionCut R₂ c * involutionCut R₁ b := by
  have h1 : R₁ * involutionCut R₂ c = involutionCut R₂ c * R₁ :=
    commute_involutionCut_of_commute hcomm c
  exact (commute_involutionCut_of_commute h1.symm b).symm

/-- **The joint corner of a commuting pair.**  The four products of spectral
cuts form a corner partition of `Matrix Y Y ℂ`. -/
theorem jointCorner_two_isCornerPartition {R₁ R₂ : Matrix Y Y ℂ}
    (hR₁ : IsExactInvolution R₁) (hR₂ : IsExactInvolution R₂)
    (hcomm : R₁ * R₂ = R₂ * R₁) :
    (∀ p : Bool × Bool, IsOrthogonalProjectionMatrix
        (cornerRefine (involutionCut R₁) (involutionCut R₂) p)) ∧
      (∀ p q : Bool × Bool, p ≠ q →
        cornerRefine (involutionCut R₁) (involutionCut R₂) p *
          cornerRefine (involutionCut R₁) (involutionCut R₂) q = 0) ∧
      ∑ p : Bool × Bool,
        cornerRefine (involutionCut R₁) (involutionCut R₂) p = 1 := by
  refine ⟨?_, ?_, ?_⟩
  · exact cornerRefine_isOrthogonalProjectionMatrix _ _
      (involutionCut_isOrthogonalProjection hR₁)
      (involutionCut_isOrthogonalProjection hR₂)
      (involutionCut_commute hcomm)
  · exact cornerRefine_orthogonal _ _ (involutionCut_orthogonal hR₁)
      (involutionCut_orthogonal hR₂) (involutionCut_commute hcomm)
  · exact cornerRefine_sum _ _ (involutionCut_sum R₁) (involutionCut_sum R₂)

/-- **The two-involution case of the manuscript's Step 1 compression.**
Compression along the four joint spectral blocks of a commuting pair is the
composite of the two block averages, which is
`CollapseJointCorner.jointCompression` at a two-element list. -/
theorem cornerCompression_jointCorner_two {R₁ R₂ : Matrix Y Y ℂ}
    (hcomm : R₁ * R₂ = R₂ * R₁) (x : Matrix Y Y ℂ) :
    cornerCompression (cornerRefine (involutionCut R₁) (involutionCut R₂)) x
      = blockAverage R₁ (blockAverage R₂ x) := by
  rw [cornerCompression_cornerRefine _ _ (involutionCut_commute hcomm) x,
    cornerCompression_involutionCut, cornerCompression_involutionCut]

/-- The same statement with the joint compression of
`Sofic/CollapseJointCorner.lean` on the right-hand side: for a two-element
window the manuscript's joint-corner compression and the composite of the
elementary block averages are the same matrix. -/
theorem cornerCompression_jointCorner_two_eq_jointCompression
    {ι : Type*} (R : ι → Matrix Y Y ℂ) (i j : ι)
    (hcomm : R i * R j = R j * R i) (x : Matrix Y Y ℂ) :
    cornerCompression (cornerRefine (involutionCut (R i)) (involutionCut (R j))) x
      = jointCompression R [i, j] x := by
  rw [cornerCompression_jointCorner_two hcomm x, jointCompression_cons,
    jointCompression_cons, jointCompression_nil]

end CollapseJointCorner
end GroupApproximation
