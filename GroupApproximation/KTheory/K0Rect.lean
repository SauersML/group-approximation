import GroupApproximation.KTheory.Basic

/-!
# Stable isomorphism is rectangular Murray--von Neumann equivalence

Two cycles `x` and `y` are *rectangularly equivalent* when a single rectangular matrix
`v : Matrix (Fin y.size) (Fin x.size) A` has `vᴴ * v = x.proj` and `v * vᴴ = y.proj`.
This file proves that this one relation is exactly `Cycle.Rel`, the equivalence closure of
the three elementary moves of `Basic.lean`.

So equality in `VMonoid A` can be checked, and produced, by exhibiting one partial isometry
between the two projections, with no chain of moves. The proof is `*`-ring algebra over any
`NonUnitalSemiring` with a `StarRing` structure.

* `Cycle.RectMvN.of_rel`: every elementary move is implemented by a rectangular matrix, and
  implementers compose (`w * v`) and add (block sums).
* `Cycle.rel_of_rectMvN`: pad `x` by a zero block of size `y.size` and `y` by one of size
  `x.size`; the off-diagonal block matrix built from `v` is then a square
  Murray--von Neumann implementer between the padded cycles.
-/

namespace GroupApproximation
namespace KTheory

open Matrix

section RectBlockSum

variable {A : Type*}

/-- The block sum of two rectangular matrices. -/
def rectBlockSum [Zero A] {m m' n n' : ℕ} (v : Matrix (Fin m') (Fin m) A)
    (w : Matrix (Fin n') (Fin n) A) : Matrix (Fin (m' + n')) (Fin (m + n)) A :=
  Matrix.reindex finSumFinEquiv finSumFinEquiv (Matrix.fromBlocks v 0 0 w)

theorem rectBlockSum_eq_blockSum [Zero A] {m n : ℕ} (p : Matrix (Fin m) (Fin m) A)
    (q : Matrix (Fin n) (Fin n) A) : rectBlockSum p q = blockSum p q := rfl

theorem conjTranspose_rectBlockSum [NonUnitalNonAssocSemiring A] [StarRing A] {m m' n n' : ℕ}
    (v : Matrix (Fin m') (Fin m) A) (w : Matrix (Fin n') (Fin n) A) :
    (rectBlockSum v w)ᴴ = rectBlockSum vᴴ wᴴ := by
  simp [rectBlockSum, Matrix.fromBlocks_conjTranspose]

theorem rectBlockSum_mul_rectBlockSum [NonUnitalNonAssocSemiring A] {m m' m'' n n' n'' : ℕ}
    (v' : Matrix (Fin m'') (Fin m') A) (w' : Matrix (Fin n'') (Fin n') A)
    (v : Matrix (Fin m') (Fin m) A) (w : Matrix (Fin n') (Fin n) A) :
    rectBlockSum v' w' * rectBlockSum v w = rectBlockSum (v' * v) (w' * w) := by
  simp [rectBlockSum, Matrix.fromBlocks_multiply]

end RectBlockSum

namespace Cycle

variable {A : Type*} [NonUnitalSemiring A] [StarRing A]

/-- **Rectangular Murray--von Neumann equivalence** of cycles: one rectangular matrix
implements both projections. -/
def RectMvN (x y : Cycle A) : Prop :=
  ∃ v : Matrix (Fin y.size) (Fin x.size) A, vᴴ * v = x.proj ∧ v * vᴴ = y.proj

theorem RectMvN.refl (x : Cycle A) : RectMvN x x := by
  refine ⟨x.proj, ?_, ?_⟩ <;>
    rw [← Matrix.star_eq_conjTranspose, x.isProj.isSelfAdjoint.star_eq,
      x.isProj.isIdempotentElem.eq]

theorem RectMvN.symm {x y : Cycle A} (h : RectMvN x y) : RectMvN y x := by
  obtain ⟨v, hv₁, hv₂⟩ := h
  exact ⟨vᴴ, by rw [conjTranspose_conjTranspose]; exact hv₂,
    by rw [conjTranspose_conjTranspose]; exact hv₁⟩

theorem RectMvN.trans {x y z : Cycle A} (h₁ : RectMvN x y) (h₂ : RectMvN y z) :
    RectMvN x z := by
  obtain ⟨v, hv₁, hv₂⟩ := h₁
  obtain ⟨w, hw₁, hw₂⟩ := h₂
  refine ⟨w * v, ?_, ?_⟩
  · rw [conjTranspose_mul]
    calc vᴴ * wᴴ * (w * v) = vᴴ * (wᴴ * w) * v := by simp only [Matrix.mul_assoc]
      _ = vᴴ * (v * vᴴ) * v := by rw [hw₁, hv₂]
      _ = vᴴ * v * (vᴴ * v) := by simp only [Matrix.mul_assoc]
      _ = x.proj := by rw [hv₁]; exact x.isProj.isIdempotentElem.eq
  · rw [conjTranspose_mul]
    calc w * v * (vᴴ * wᴴ) = w * (v * vᴴ) * wᴴ := by simp only [Matrix.mul_assoc]
      _ = w * (wᴴ * w) * wᴴ := by rw [hv₂, hw₁]
      _ = w * wᴴ * (w * wᴴ) := by simp only [Matrix.mul_assoc]
      _ = z.proj := by rw [hw₂]; exact z.isProj.isIdempotentElem.eq

theorem RectMvN.add {x x' y y' : Cycle A} (hx : RectMvN x x') (hy : RectMvN y y') :
    RectMvN (x + y) (x' + y') := by
  obtain ⟨v, hv₁, hv₂⟩ := hx
  obtain ⟨w, hw₁, hw₂⟩ := hy
  refine ⟨rectBlockSum v w, ?_, ?_⟩
  · show (rectBlockSum v w)ᴴ * rectBlockSum v w = blockSum x.proj y.proj
    rw [conjTranspose_rectBlockSum, rectBlockSum_mul_rectBlockSum, hv₁, hw₁,
      rectBlockSum_eq_blockSum]
  · show rectBlockSum v w * (rectBlockSum v w)ᴴ = blockSum x'.proj y'.proj
    rw [conjTranspose_rectBlockSum, rectBlockSum_mul_rectBlockSum, hv₂, hw₂,
      rectBlockSum_eq_blockSum]

/-- The empty cycle is equivalent to a zero projection of any size. -/
theorem rectMvN_zero_pad (a : ℕ) :
    RectMvN (0 : Cycle A) ⟨a, 0, IsStarProjection.zero _⟩ :=
  ⟨0, Matrix.mul_zero _, Matrix.zero_mul _⟩

/-- Each elementary move is implemented by a rectangular matrix. -/
theorem RectMvN.of_step {x y : Cycle A} (h : Step x y) : RectMvN x y := by
  cases h with
  | @mvn n p q hp hq hpq =>
      obtain ⟨v, hv₁, hv₂⟩ := hpq
      exact ⟨v, hv₁, hv₂⟩
  | @reindex n m p hp e =>
      refine ⟨p.submatrix e id, ?_, ?_⟩
      · show (p.submatrix e id)ᴴ * p.submatrix e id = p
        rw [conjTranspose_submatrix, ← submatrix_mul pᴴ p id e id e.bijective,
          ← star_eq_conjTranspose, hp.isSelfAdjoint.star_eq, hp.isIdempotentElem.eq,
          submatrix_id_id]
      · show p.submatrix e id * (p.submatrix e id)ᴴ = p.submatrix e e
        rw [conjTranspose_submatrix, ← submatrix_mul p pᴴ e id e Function.bijective_id,
          ← star_eq_conjTranspose, hp.isSelfAdjoint.star_eq, hp.isIdempotentElem.eq]
  | @pad n p hp a =>
      have h := RectMvN.add (RectMvN.refl (⟨n, p, hp⟩ : Cycle A)) (rectMvN_zero_pad (A := A) a)
      rw [add_zero_cycle] at h
      exact h

/-- Stable isomorphism implies rectangular equivalence. -/
theorem RectMvN.of_rel {x y : Cycle A} (h : Rel x y) : RectMvN x y := by
  induction h with
  | rel _ _ hxy => exact RectMvN.of_step hxy
  | refl x => exact RectMvN.refl x
  | symm _ _ _ ih => exact ih.symm
  | trans _ _ _ _ _ ih₁ ih₂ => exact ih₁.trans ih₂

/-- The off-diagonal implementer: a rectangular implementer `v` of `p ~ q` gives a square
implementer of `p ⊞ 0 ~ 0 ⊞ q`. -/
theorem murrayVonNeumannEquiv_blockSum_zero_zero_blockSum {m n : ℕ}
    {p : Matrix (Fin n) (Fin n) A} {q : Matrix (Fin m) (Fin m) A}
    (v : Matrix (Fin m) (Fin n) A) (hv₁ : vᴴ * v = p) (hv₂ : v * vᴴ = q) :
    MurrayVonNeumannEquiv (blockSum p (0 : Matrix (Fin m) (Fin m) A))
      (blockSum (0 : Matrix (Fin n) (Fin n) A) q) := by
  refine ⟨Matrix.reindex finSumFinEquiv finSumFinEquiv
    (Matrix.fromBlocks (0 : Matrix (Fin n) (Fin n) A) 0 v 0), ?_, ?_⟩
  · simp [Matrix.star_eq_conjTranspose, Matrix.fromBlocks_conjTranspose,
      Matrix.fromBlocks_multiply, blockSum, hv₁]
  · simp [Matrix.star_eq_conjTranspose, Matrix.fromBlocks_conjTranspose,
      Matrix.fromBlocks_multiply, blockSum, hv₂]

/-- **Rectangular equivalence implies stable isomorphism.** -/
theorem rel_of_rectMvN {x y : Cycle A} (h : RectMvN x y) : Rel x y := by
  obtain ⟨n, p, hp⟩ := x
  obtain ⟨m, q, hq⟩ := y
  obtain ⟨v, hv₁, hv₂⟩ := h
  have h₁ : Rel (⟨n, p, hp⟩ : Cycle A)
      ⟨n + m, blockSum p (0 : Matrix (Fin m) (Fin m) A),
        isStarProjection_blockSum hp (IsStarProjection.zero _)⟩ :=
    rel_of_step (Step.pad m)
  have h₂ : Rel (⟨n + m, blockSum p (0 : Matrix (Fin m) (Fin m) A),
        isStarProjection_blockSum hp (IsStarProjection.zero _)⟩ : Cycle A)
      ⟨n + m, blockSum (0 : Matrix (Fin n) (Fin n) A) q,
        isStarProjection_blockSum (IsStarProjection.zero _) hq⟩ :=
    rel_of_step (Step.mvn
      (murrayVonNeumannEquiv_blockSum_zero_zero_blockSum (p := p) (q := q) v hv₁ hv₂))
  have h₃ : Rel (⟨m, q, hq⟩ : Cycle A)
      ⟨m + n, blockSum q (0 : Matrix (Fin n) (Fin n) A),
        isStarProjection_blockSum hq (IsStarProjection.zero _)⟩ :=
    rel_of_step (Step.pad n)
  have h₄ : Rel (⟨m + n, blockSum q (0 : Matrix (Fin n) (Fin n) A),
        isStarProjection_blockSum hq (IsStarProjection.zero _)⟩ : Cycle A)
      ⟨n + m, blockSum (0 : Matrix (Fin n) (Fin n) A) q,
        isStarProjection_blockSum (IsStarProjection.zero _) hq⟩ :=
    rel_reindex_eq _ _ (finSumSwap n m) (blockSum_comm q 0)
  exact rel_trans h₁ (rel_trans h₂ (rel_symm (rel_trans h₃ h₄)))

/-- **Stable isomorphism is rectangular Murray--von Neumann equivalence.** -/
theorem rel_iff_rectMvN {x y : Cycle A} : Rel x y ↔ RectMvN x y :=
  ⟨RectMvN.of_rel, rel_of_rectMvN⟩

/-- A zero projection of any size presents the zero class. -/
theorem rel_zero_proj (n : ℕ) : Rel (⟨n, 0, IsStarProjection.zero _⟩ : Cycle A) 0 :=
  rel_of_rectMvN ⟨0, Matrix.mul_zero _, Matrix.zero_mul _⟩

end Cycle

end KTheory
end GroupApproximation
