import GroupApproximation.Analysis.LanceBlockOperator

/-!
# The block Hilbert space over an arbitrary coefficient space

`Analysis/LanceBlockOperator` builds the projections, inclusions and block
operator of `PiLp 2 (fun _ : Fin n ↦ ℂᵏ)`.  Nothing in those proofs uses
finite-dimensionality of the coefficient space: they are the adjoint of
`PiLp.proj`, the `PiLp` single, and `PiLp.inner_apply`.  This module repeats
them over an arbitrary complex Hilbert space `E`, which is what the `M₂`
amplification of Shulman's `𝒟` needs — there the coefficient space is the
`H` the models already act on.

`Analysis/ShulmanFillNormingBlockHom` turns `blockOp` into a
`*`-homomorphism; together they are the supplier of the four hypotheses on the
conjugating unitary of
`Analysis/ShulmanFillNormingConjugationLift.conjugate`, because the flip
`((0,1),(1,0))` is a unitary of `M₂` over the models.
-/

namespace GroupApproximation
namespace ShulmanFill

open scoped InnerProductSpace

noncomputable section

section BlockHilbert

variable {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
variable [CompleteSpace E] {n : ℕ}

/-- The block Hilbert space `E ⊕ ⋯ ⊕ E`, `n` summands. -/
abbrev BlockSpace (E : Type) [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    (n : ℕ) : Type :=
  PiLp 2 (fun _ : Fin n ↦ E)

/-- The projection onto the `i`-th summand. -/
def hBlockProj (E : Type) [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    (n : ℕ) (i : Fin n) : BlockSpace E n →L[ℂ] E :=
  PiLp.proj 2 (fun _ : Fin n ↦ E) i

omit [CompleteSpace E] in
@[simp] theorem hBlockProj_apply (i : Fin n) (w : BlockSpace E n) :
    hBlockProj E n i w = w i := rfl

/-- The inclusion of the `i`-th summand, as the adjoint of the projection. -/
def hBlockIncl (E : Type) [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    [CompleteSpace E] (n : ℕ) (i : Fin n) : E →L[ℂ] BlockSpace E n :=
  ContinuousLinearMap.adjoint (hBlockProj E n i)

theorem adjoint_hBlockIncl (i : Fin n) :
    ContinuousLinearMap.adjoint (hBlockIncl E n i) = hBlockProj E n i := by
  rw [hBlockIncl, ContinuousLinearMap.adjoint_adjoint]

theorem inner_hBlockIncl_right (i : Fin n) (w : BlockSpace E n) (x : E) :
    ⟪w, hBlockIncl E n i x⟫_ℂ = ⟪w i, x⟫_ℂ := by
  rw [hBlockIncl, ContinuousLinearMap.adjoint_inner_right]
  rfl

theorem inner_hBlockIncl_left (i : Fin n) (x : E) (w : BlockSpace E n) :
    ⟪hBlockIncl E n i x, w⟫_ℂ = ⟪x, w i⟫_ℂ := by
  rw [hBlockIncl, ContinuousLinearMap.adjoint_inner_left]
  rfl

omit [CompleteSpace E] in
/-- The block inner product is the sum of the coordinate inner products. -/
theorem inner_block_eq_sum (v w : BlockSpace E n) :
    ⟪v, w⟫_ℂ = ∑ i : Fin n, ⟪v i, w i⟫_ℂ :=
  PiLp.inner_apply v w

/-- The inclusion hits the `PiLp` single. -/
theorem hBlockIncl_eq_single (i : Fin n) (x : E) :
    hBlockIncl E n i x =
      PiLp.single (p := 2) (β := fun _ : Fin n ↦ E) i x := by
  refine ext_inner_left ℂ fun v ↦ ?_
  rw [inner_hBlockIncl_right]
  have h2 : ⟪v, PiLp.single (p := 2) (β := fun _ : Fin n ↦ E) i x⟫_ℂ
      = ∑ j : Fin n,
        ⟪v j, PiLp.single (p := 2) (β := fun _ : Fin n ↦ E) i x j⟫_ℂ :=
    inner_block_eq_sum v (PiLp.single (p := 2) (β := fun _ : Fin n ↦ E) i x)
  have h3 : ∑ j : Fin n,
      ⟪v j, PiLp.single (p := 2) (β := fun _ : Fin n ↦ E) i x j⟫_ℂ
      = ⟪v i, PiLp.single (p := 2) (β := fun _ : Fin n ↦ E) i x i⟫_ℂ := by
    refine Finset.sum_eq_single i (fun j _ hj ↦ ?_)
      (fun h ↦ absurd (Finset.mem_univ i) h)
    rw [PiLp.single_eq_of_ne (p := 2) (β := fun _ : Fin n ↦ E) hj,
      inner_zero_right]
  rw [h2, h3, PiLp.single_eq_same (p := 2) (β := fun _ : Fin n ↦ E)]

theorem hBlockIncl_coord_same (i : Fin n) (x : E) :
    hBlockIncl E n i x i = x := by
  rw [hBlockIncl_eq_single]
  exact PiLp.single_eq_same (p := 2) (β := fun _ : Fin n ↦ E) i x

theorem hBlockIncl_coord_ne {i j : Fin n} (h : j ≠ i) (x : E) :
    hBlockIncl E n i x j = 0 := by
  rw [hBlockIncl_eq_single]
  exact PiLp.single_eq_of_ne (p := 2) (β := fun _ : Fin n ↦ E) h x

/-- **The projections and inclusions are matrix units.**  `π_i ∘ ι_j` is the
identity when `i = j` and zero otherwise; this is what makes the block operator
multiplicative. -/
theorem hBlockProj_comp_hBlockIncl_same (i : Fin n) :
    (hBlockProj E n i).comp (hBlockIncl E n i) =
      (1 : E →L[ℂ] E) := by
  refine ContinuousLinearMap.ext fun x ↦ ?_
  show hBlockIncl E n i x i = x
  exact hBlockIncl_coord_same i x

theorem hBlockProj_comp_hBlockIncl_ne {i j : Fin n} (h : i ≠ j) :
    (hBlockProj E n i).comp (hBlockIncl E n j) = 0 := by
  refine ContinuousLinearMap.ext fun x ↦ ?_
  show hBlockIncl E n j x i = 0
  exact hBlockIncl_coord_ne h x

/-- The block decomposition of the identity. -/
theorem sum_hBlockIncl_comp_hBlockProj :
    (∑ r : Fin n, (hBlockIncl E n r).comp (hBlockProj E n r)) =
      (1 : BlockSpace E n →L[ℂ] BlockSpace E n) := by
  refine ContinuousLinearMap.ext fun w ↦ ?_
  rw [sum_apply]
  refine ext_inner_left ℂ fun v ↦ ?_
  rw [inner_sum]
  have hterm : ∀ r : Fin n,
      ⟪v, ((hBlockIncl E n r).comp (hBlockProj E n r)) w⟫_ℂ = ⟪v r, w r⟫_ℂ := by
    intro r
    have h : ((hBlockIncl E n r).comp (hBlockProj E n r)) w
        = hBlockIncl E n r (w r) := rfl
    rw [h, inner_hBlockIncl_right]
  rw [Finset.sum_congr rfl fun r _ ↦ hterm r]
  have hone : ((1 : BlockSpace E n →L[ℂ] BlockSpace E n) w) = w := rfl
  rw [hone]
  exact (inner_block_eq_sum v w).symm

/-- **A matrix of operators as one operator on the block space.** -/
def hBlockOp (X : CStarMatrix (Fin n) (Fin n) (E →L[ℂ] E)) :
    BlockSpace E n →L[ℂ] BlockSpace E n :=
  ∑ i : Fin n, ∑ j : Fin n,
    (hBlockIncl E n i).comp ((X i j).comp (hBlockProj E n j))

theorem hBlockOp_apply (X : CStarMatrix (Fin n) (Fin n) (E →L[ℂ] E))
    (w : BlockSpace E n) :
    hBlockOp X w =
      ∑ i : Fin n, ∑ j : Fin n, hBlockIncl E n i ((X i j) (w j)) := by
  rw [hBlockOp, sum_apply]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  rw [sum_apply]
  exact Finset.sum_congr rfl fun j _ ↦ rfl

end BlockHilbert

end

end ShulmanFill
end GroupApproximation
