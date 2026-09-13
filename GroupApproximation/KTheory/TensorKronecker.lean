import GroupApproximation.KTheory.BlockMoves
import Mathlib.LinearAlgebra.Matrix.Kronecker

/-!
# Kronecker products of projection matrices along a star pairing

The external product on `K₀` sends `[p] ⊗ [q]` to `[p ⊗ q]`, the Kronecker product of the two
projection matrices with entries paired into a third algebra.  Everything the descent to `K₀`
needs is a statement about Kronecker products of square matrices over a pairing
`μ : A × B → C` that is additive in each variable, multiplicative in both variables at once,
and compatible with the adjoint (`StarPairing`):

* `kron_mul_kron`, `star_kron`: `p ⊗ q` is a projection, and implementers transport;
* `kron_submatrix_left/right`: reindexing a factor reindexes the product;
* `kron_zero_left/right`, `kron_blockSum_left/right`: padding and block sums distribute,
  up to the explicit reindexings `finProdSumLeft/Right`.

The motivating pairing is `a, b ↦ a ⊗ b` into a C*-tensor product, but nothing here uses norms.
Products are indexed by `Fin (m * n)` through `finProdFinEquiv`, so that they are again cycles.
-/

namespace GroupApproximation
namespace KTheory

open Matrix

/-- A pairing `A × B → C` that is additive in each variable, multiplicative in both variables at
once, and compatible with the adjoint: the algebraic content of `a, b ↦ a ⊗ b`. -/
structure StarPairing (A B C : Type*) [NonUnitalSemiring A] [StarRing A] [NonUnitalSemiring B]
    [StarRing B] [NonUnitalSemiring C] [StarRing C] where
  /-- The underlying bi-additive map. -/
  toFun : A →+ B →+ C
  map_mul' : ∀ a a' b b', toFun (a * a') (b * b') = toFun a b * toFun a' b'
  map_star' : ∀ a b, toFun (star a) (star b) = star (toFun a b)

section NonUnital

variable {A B C : Type*} [NonUnitalSemiring A] [StarRing A] [NonUnitalSemiring B] [StarRing B]
  [NonUnitalSemiring C] [StarRing C] (μ : StarPairing A B C) {m m' n n' : ℕ}

theorem StarPairing.toFun_sum_sum {ι κ : Type*} (s : Finset ι) (t : Finset κ) (f : ι → A)
    (g : κ → B) :
    μ.toFun (∑ i ∈ s, f i) (∑ k ∈ t, g k) = ∑ i ∈ s, ∑ k ∈ t, μ.toFun (f i) (g k) := by
  rw [map_sum μ.toFun, AddMonoidHom.finsetSum_apply]
  exact Finset.sum_congr rfl fun i _ => map_sum (μ.toFun (f i)) g t

/-- The Kronecker product of square matrices along `μ`, indexed by `Fin (m * n)`. -/
def kron (p : Matrix (Fin m) (Fin m) A) (q : Matrix (Fin n) (Fin n) B) :
    Matrix (Fin (m * n)) (Fin (m * n)) C :=
  (Matrix.kroneckerMap (fun a b => μ.toFun a b) p q).submatrix finProdFinEquiv.symm
    finProdFinEquiv.symm

theorem kron_apply (p : Matrix (Fin m) (Fin m) A) (q : Matrix (Fin n) (Fin n) B)
    (i j : Fin m) (k l : Fin n) :
    kron μ p q (finProdFinEquiv (i, k)) (finProdFinEquiv (j, l)) = μ.toFun (p i j) (q k l) := by
  simp only [kron, Matrix.submatrix_apply, Equiv.symm_apply_apply, Matrix.kroneckerMap_apply]

theorem kron_mul_kron (p p' : Matrix (Fin m) (Fin m) A) (q q' : Matrix (Fin n) (Fin n) B) :
    kron μ p q * kron μ p' q' = kron μ (p * p') (q * q') := by
  simp only [kron]
  rw [Matrix.submatrix_mul_equiv]
  congr 1
  ext ⟨i, k⟩ ⟨j, l⟩
  simp only [Matrix.mul_apply, Matrix.kroneckerMap_apply, Fintype.sum_prod_type,
    μ.toFun_sum_sum, μ.map_mul']

theorem star_kron (p : Matrix (Fin m) (Fin m) A) (q : Matrix (Fin n) (Fin n) B) :
    star (kron μ p q) = kron μ (star p) (star q) := by
  ext i j
  obtain ⟨⟨i₁, i₂⟩, rfl⟩ := finProdFinEquiv.surjective i
  obtain ⟨⟨j₁, j₂⟩, rfl⟩ := finProdFinEquiv.surjective j
  simp only [Matrix.star_apply, kron_apply, μ.map_star']

theorem isStarProjection_kron {p : Matrix (Fin m) (Fin m) A} {q : Matrix (Fin n) (Fin n) B}
    (hp : IsStarProjection p) (hq : IsStarProjection q) : IsStarProjection (kron μ p q) := by
  refine ⟨?_, ?_⟩
  · show kron μ p q * kron μ p q = kron μ p q
    rw [kron_mul_kron, hp.isIdempotentElem.eq, hq.isIdempotentElem.eq]
  · show star (kron μ p q) = kron μ p q
    rw [star_kron, hp.isSelfAdjoint.star_eq, hq.isSelfAdjoint.star_eq]

/-- An implementer of `p ~ p'` tensored with a projection implements `p ⊗ q ~ p' ⊗ q`. -/
theorem murrayVonNeumannEquiv_kron_left {p p' : Matrix (Fin m) (Fin m) A}
    {q : Matrix (Fin n) (Fin n) B} (h : MurrayVonNeumannEquiv p p') (hq : IsStarProjection q) :
    MurrayVonNeumannEquiv (kron μ p q) (kron μ p' q) := by
  obtain ⟨v, hv₁, hv₂⟩ := h
  refine ⟨kron μ v q, ?_, ?_⟩
  · rw [star_kron, kron_mul_kron, hv₁, hq.isSelfAdjoint.star_eq, hq.isIdempotentElem.eq]
  · rw [star_kron, kron_mul_kron, hv₂, hq.isSelfAdjoint.star_eq, hq.isIdempotentElem.eq]

theorem murrayVonNeumannEquiv_kron_right {p : Matrix (Fin m) (Fin m) A}
    {q q' : Matrix (Fin n) (Fin n) B} (hp : IsStarProjection p) (h : MurrayVonNeumannEquiv q q') :
    MurrayVonNeumannEquiv (kron μ p q) (kron μ p q') := by
  obtain ⟨w, hw₁, hw₂⟩ := h
  refine ⟨kron μ p w, ?_, ?_⟩
  · rw [star_kron, kron_mul_kron, hw₁, hp.isSelfAdjoint.star_eq, hp.isIdempotentElem.eq]
  · rw [star_kron, kron_mul_kron, hw₂, hp.isSelfAdjoint.star_eq, hp.isIdempotentElem.eq]

/-! ## Reindexing a factor -/

/-- The reindexing of `Fin (m * n)` induced by reindexings of the two factors. -/
def finProdCongr (e : Fin m ≃ Fin m') (f : Fin n ≃ Fin n') : Fin (m * n) ≃ Fin (m' * n') :=
  finProdFinEquiv.symm.trans ((e.prodCongr f).trans finProdFinEquiv)

theorem finProdCongr_apply (e : Fin m ≃ Fin m') (f : Fin n ≃ Fin n') (i : Fin m) (k : Fin n) :
    finProdCongr e f (finProdFinEquiv (i, k)) = finProdFinEquiv (e i, f k) := by
  simp only [finProdCongr, Equiv.trans_apply, Equiv.symm_apply_apply, Equiv.prodCongr_apply,
    Prod.map_apply]

theorem kron_submatrix_left (e : Fin m' ≃ Fin m) (p : Matrix (Fin m) (Fin m) A)
    (q : Matrix (Fin n) (Fin n) B) :
    kron μ (p.submatrix e e) q =
      (kron μ p q).submatrix (finProdCongr e (Equiv.refl (Fin n)))
        (finProdCongr e (Equiv.refl (Fin n))) := by
  ext i j
  obtain ⟨⟨i₁, i₂⟩, rfl⟩ := finProdFinEquiv.surjective i
  obtain ⟨⟨j₁, j₂⟩, rfl⟩ := finProdFinEquiv.surjective j
  simp only [kron_apply, Matrix.submatrix_apply, finProdCongr_apply, Equiv.refl_apply]

theorem kron_submatrix_right (e : Fin n' ≃ Fin n) (p : Matrix (Fin m) (Fin m) A)
    (q : Matrix (Fin n) (Fin n) B) :
    kron μ p (q.submatrix e e) =
      (kron μ p q).submatrix (finProdCongr (Equiv.refl (Fin m)) e)
        (finProdCongr (Equiv.refl (Fin m)) e) := by
  ext i j
  obtain ⟨⟨i₁, i₂⟩, rfl⟩ := finProdFinEquiv.surjective i
  obtain ⟨⟨j₁, j₂⟩, rfl⟩ := finProdFinEquiv.surjective j
  simp only [kron_apply, Matrix.submatrix_apply, finProdCongr_apply, Equiv.refl_apply]

/-! ## Padding and block sums -/

theorem kron_zero_left (q : Matrix (Fin n) (Fin n) B) :
    kron μ (0 : Matrix (Fin m) (Fin m) A) q = 0 := by
  ext i j
  obtain ⟨⟨i₁, i₂⟩, rfl⟩ := finProdFinEquiv.surjective i
  obtain ⟨⟨j₁, j₂⟩, rfl⟩ := finProdFinEquiv.surjective j
  simp only [kron_apply, Matrix.zero_apply, map_zero, AddMonoidHom.zero_apply]

theorem kron_zero_right (p : Matrix (Fin m) (Fin m) A) :
    kron μ p (0 : Matrix (Fin n) (Fin n) B) = 0 := by
  ext i j
  obtain ⟨⟨i₁, i₂⟩, rfl⟩ := finProdFinEquiv.surjective i
  obtain ⟨⟨j₁, j₂⟩, rfl⟩ := finProdFinEquiv.surjective j
  simp only [kron_apply, Matrix.zero_apply, map_zero]

/-- `Fin ((m + m') * n) ≃ Fin (m * n + m' * n)`: the product distributes over the block sum. -/
def finProdSumLeft (m m' n : ℕ) : Fin ((m + m') * n) ≃ Fin (m * n + m' * n) :=
  finProdFinEquiv.symm.trans (((finSumFinEquiv.symm.prodCongr (Equiv.refl (Fin n))).trans
    (Equiv.sumProdDistrib _ _ _)).trans ((finProdFinEquiv.sumCongr finProdFinEquiv).trans
      finSumFinEquiv))

theorem finProdSumLeft_castAdd (i : Fin m) (k : Fin n) :
    finProdSumLeft m m' n (finProdFinEquiv (Fin.castAdd m' i, k)) =
      Fin.castAdd (m' * n) (finProdFinEquiv (i, k)) := by
  simp only [finProdSumLeft, Equiv.trans_apply, Equiv.symm_apply_apply, Equiv.prodCongr_apply,
    Prod.map_apply, finSumFinEquiv_symm_apply_castAdd, Equiv.refl_apply,
    Equiv.sumProdDistrib_apply_left, Equiv.sumCongr_apply, Sum.map_inl, finSumFinEquiv_apply_left]

theorem finProdSumLeft_natAdd (i : Fin m') (k : Fin n) :
    finProdSumLeft m m' n (finProdFinEquiv (Fin.natAdd m i, k)) =
      Fin.natAdd (m * n) (finProdFinEquiv (i, k)) := by
  simp only [finProdSumLeft, Equiv.trans_apply, Equiv.symm_apply_apply, Equiv.prodCongr_apply,
    Prod.map_apply, finSumFinEquiv_symm_apply_natAdd, Equiv.refl_apply,
    Equiv.sumProdDistrib_apply_right, Equiv.sumCongr_apply, Sum.map_inr,
    finSumFinEquiv_apply_right]

/-- `Fin (m * (n + n')) ≃ Fin (m * n + m * n')`: the product distributes over the block sum. -/
def finProdSumRight (m n n' : ℕ) : Fin (m * (n + n')) ≃ Fin (m * n + m * n') :=
  finProdFinEquiv.symm.trans ((((Equiv.refl (Fin m)).prodCongr finSumFinEquiv.symm).trans
    (Equiv.prodSumDistrib _ _ _)).trans ((finProdFinEquiv.sumCongr finProdFinEquiv).trans
      finSumFinEquiv))

theorem finProdSumRight_castAdd (i : Fin m) (k : Fin n) :
    finProdSumRight m n n' (finProdFinEquiv (i, Fin.castAdd n' k)) =
      Fin.castAdd (m * n') (finProdFinEquiv (i, k)) := by
  simp only [finProdSumRight, Equiv.trans_apply, Equiv.symm_apply_apply, Equiv.prodCongr_apply,
    Prod.map_apply, finSumFinEquiv_symm_apply_castAdd, Equiv.refl_apply,
    Equiv.prodSumDistrib_apply_left, Equiv.sumCongr_apply, Sum.map_inl, finSumFinEquiv_apply_left]

theorem finProdSumRight_natAdd (i : Fin m) (k : Fin n') :
    finProdSumRight m n n' (finProdFinEquiv (i, Fin.natAdd n k)) =
      Fin.natAdd (m * n) (finProdFinEquiv (i, k)) := by
  simp only [finProdSumRight, Equiv.trans_apply, Equiv.symm_apply_apply, Equiv.prodCongr_apply,
    Prod.map_apply, finSumFinEquiv_symm_apply_natAdd, Equiv.refl_apply,
    Equiv.prodSumDistrib_apply_right, Equiv.sumCongr_apply, Sum.map_inr,
    finSumFinEquiv_apply_right]

theorem kron_blockSum_left (p : Matrix (Fin m) (Fin m) A) (p' : Matrix (Fin m') (Fin m') A)
    (q : Matrix (Fin n) (Fin n) B) :
    (blockSum (kron μ p q) (kron μ p' q)).submatrix (finProdSumLeft m m' n)
      (finProdSumLeft m m' n) = kron μ (blockSum p p') q := by
  ext i j
  obtain ⟨⟨i₁, i₂⟩, rfl⟩ := finProdFinEquiv.surjective i
  obtain ⟨⟨j₁, j₂⟩, rfl⟩ := finProdFinEquiv.surjective j
  induction i₁ using Fin.addCases <;> induction j₁ using Fin.addCases <;>
    simp only [Matrix.submatrix_apply, finProdSumLeft_castAdd, finProdSumLeft_natAdd,
      blockSum_apply_castAdd_castAdd, blockSum_apply_castAdd_natAdd,
      blockSum_apply_natAdd_castAdd, blockSum_apply_natAdd_natAdd, kron_apply, map_zero,
      AddMonoidHom.zero_apply]

theorem kron_blockSum_right (p : Matrix (Fin m) (Fin m) A) (q : Matrix (Fin n) (Fin n) B)
    (q' : Matrix (Fin n') (Fin n') B) :
    (blockSum (kron μ p q) (kron μ p q')).submatrix (finProdSumRight m n n')
      (finProdSumRight m n n') = kron μ p (blockSum q q') := by
  ext i j
  obtain ⟨⟨i₁, i₂⟩, rfl⟩ := finProdFinEquiv.surjective i
  obtain ⟨⟨j₁, j₂⟩, rfl⟩ := finProdFinEquiv.surjective j
  induction i₂ using Fin.addCases <;> induction j₂ using Fin.addCases <;>
    simp only [Matrix.submatrix_apply, finProdSumRight_castAdd, finProdSumRight_natAdd,
      blockSum_apply_castAdd_castAdd, blockSum_apply_castAdd_natAdd,
      blockSum_apply_natAdd_castAdd, blockSum_apply_natAdd_natAdd, kron_apply, map_zero]

end NonUnital

section Unital

variable {A B C : Type*} [Semiring A] [StarRing A] [Semiring B] [StarRing B] [Semiring C]
  [StarRing C] {m n : ℕ}

/-- A unital pairing carries the pair of identity matrices to the identity matrix. -/
theorem kron_one_one (μ : StarPairing A B C) (h : μ.toFun 1 1 = 1) :
    kron μ (1 : Matrix (Fin m) (Fin m) A) (1 : Matrix (Fin n) (Fin n) B) = 1 := by
  ext i j
  obtain ⟨⟨i₁, i₂⟩, rfl⟩ := finProdFinEquiv.surjective i
  obtain ⟨⟨j₁, j₂⟩, rfl⟩ := finProdFinEquiv.surjective j
  rw [kron_apply]
  by_cases h₁ : i₁ = j₁ <;> by_cases h₂ : i₂ = j₂ <;>
    simp [Matrix.one_apply, h₁, h₂, h, EmbeddingLike.apply_eq_iff_eq]

end Unital

end KTheory
end GroupApproximation
