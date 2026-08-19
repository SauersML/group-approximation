import GroupApproximation.Analysis.CStarMatrixFactorization
import Mathlib.Analysis.InnerProductSpace.StarOrder
import Mathlib.Analysis.Normed.Lp.PiLp

/-!
# Block matrices of Hilbert-space operators, and form positivity

Toward proof-ledger row `RE.05` (the Lance debt).  The Choi reconstruction of
the Arveson extension produces matrices over `B(ℂᵏ)` whose positivity is known
only through scalar quadratic forms.  The repository's
`CStarExactness.IsCompletelyPositive` wants factorizations `star P * P` in
`CStarMatrix`; this file builds the bridge through the block-operator
representation:

* `blockOp` — a matrix `X` over `B(ℂᵏ)` as one operator on the Hilbert space
  `PiLp 2 (fun _ : Fin n ↦ ℂᵏ)`, assembled as `∑ i j, ι_i ∘ X i j ∘ π_j`;
* `inner_blockOp` — its sesquilinear form is the sum of the entry forms;
* `blockProj_comp_blockOp_comp_blockIncl` — the entries are recovered by
  compression;
* `exists_factor_of_blockOp_form_nonneg` — **the bridge**: if `star X = X`
  and the block operator has nonnegative quadratic form, then
  `X = star P * P` in `CStarMatrix`.  The factorization is the operator
  square root of the block operator (positive in the Loewner order, which on
  `B(H)` carries a global `StarOrderedRing` instance), cut back into blocks
  by the compressions.

## Manuscript status

Infrastructure for the Lance lane; certifies no manuscript step on its own.
`RE.05` remains conditional until the full compression statement lands.
-/

namespace GroupApproximation
namespace CStarExactness

open scoped InnerProductSpace

noncomputable section

variable {k n : ℕ}

/-- The projection onto the `i`-th summand of the block Hilbert space. -/
def blockProj (k n : ℕ) (i : Fin n) :
    PiLp 2 (fun _ : Fin n ↦ EuclideanSpace ℂ (Fin k)) →L[ℂ]
      EuclideanSpace ℂ (Fin k) :=
  PiLp.proj 2 (fun _ : Fin n ↦ EuclideanSpace ℂ (Fin k)) i

@[simp]
theorem blockProj_apply (i : Fin n)
    (w : PiLp 2 (fun _ : Fin n ↦ EuclideanSpace ℂ (Fin k))) :
    blockProj k n i w = w i := rfl

/-- The inclusion of the `i`-th summand, as the adjoint of the coordinate
projection. -/
def blockIncl (k n : ℕ) (i : Fin n) :
    EuclideanSpace ℂ (Fin k) →L[ℂ]
      PiLp 2 (fun _ : Fin n ↦ EuclideanSpace ℂ (Fin k)) :=
  ContinuousLinearMap.adjoint (blockProj k n i)

theorem adjoint_blockIncl (i : Fin n) :
    ContinuousLinearMap.adjoint (blockIncl k n i) = blockProj k n i := by
  rw [blockIncl, ContinuousLinearMap.adjoint_adjoint]

theorem inner_blockIncl_right (i : Fin n)
    (w : PiLp 2 (fun _ : Fin n ↦ EuclideanSpace ℂ (Fin k)))
    (x : EuclideanSpace ℂ (Fin k)) :
    ⟪w, blockIncl k n i x⟫_ℂ = ⟪w i, x⟫_ℂ := by
  rw [blockIncl, ContinuousLinearMap.adjoint_inner_right]
  rfl

theorem inner_blockIncl_left (i : Fin n)
    (x : EuclideanSpace ℂ (Fin k))
    (w : PiLp 2 (fun _ : Fin n ↦ EuclideanSpace ℂ (Fin k))) :
    ⟪blockIncl k n i x, w⟫_ℂ = ⟪x, w i⟫_ℂ := by
  rw [blockIncl, ContinuousLinearMap.adjoint_inner_left]
  rfl

/-- The block inner product is the sum of the coordinate inner products. -/
theorem inner_block_eq_sum
    (v w : PiLp 2 (fun _ : Fin n ↦ EuclideanSpace ℂ (Fin k))) :
    ⟪v, w⟫_ℂ = ∑ i : Fin n, ⟪v i, w i⟫_ℂ :=
  PiLp.inner_apply v w

/-- The inclusion hits the `PiLp` single. -/
theorem blockIncl_eq_single (i : Fin n) (x : EuclideanSpace ℂ (Fin k)) :
    blockIncl k n i x = PiLp.single (p := 2) (β := fun _ : Fin n ↦ EuclideanSpace ℂ (Fin k)) i x := by
  refine ext_inner_left ℂ fun v ↦ ?_
  rw [inner_blockIncl_right]
  have h2 : ⟪v, PiLp.single (p := 2) (β := fun _ : Fin n ↦ EuclideanSpace ℂ (Fin k)) i x⟫_ℂ
      = ∑ j : Fin n, ⟪v j, PiLp.single (p := 2) (β := fun _ : Fin n ↦ EuclideanSpace ℂ (Fin k)) i x j⟫_ℂ :=
    inner_block_eq_sum v (PiLp.single (p := 2) (β := fun _ : Fin n ↦ EuclideanSpace ℂ (Fin k)) i x)
  have h3 : ∑ j : Fin n, ⟪v j, PiLp.single (p := 2) (β := fun _ : Fin n ↦ EuclideanSpace ℂ (Fin k)) i x j⟫_ℂ
      = ⟪v i, PiLp.single (p := 2) (β := fun _ : Fin n ↦ EuclideanSpace ℂ (Fin k)) i x i⟫_ℂ := by
    refine Finset.sum_eq_single i (fun j _ hj ↦ ?_)
      (fun h ↦ absurd (Finset.mem_univ i) h)
    rw [PiLp.single_eq_of_ne (p := 2) (β := fun _ : Fin n ↦ EuclideanSpace ℂ (Fin k)) hj, inner_zero_right]
  rw [h2, h3, PiLp.single_eq_same (p := 2) (β := fun _ : Fin n ↦ EuclideanSpace ℂ (Fin k))]

theorem blockIncl_coord_same (i : Fin n) (x : EuclideanSpace ℂ (Fin k)) :
    blockIncl k n i x i = x := by
  rw [blockIncl_eq_single]
  exact PiLp.single_eq_same (p := 2) (β := fun _ : Fin n ↦ EuclideanSpace ℂ (Fin k)) i x

theorem blockIncl_coord_ne {i j : Fin n} (h : j ≠ i)
    (x : EuclideanSpace ℂ (Fin k)) :
    blockIncl k n i x j = 0 := by
  rw [blockIncl_eq_single]
  exact PiLp.single_eq_of_ne (p := 2) (β := fun _ : Fin n ↦ EuclideanSpace ℂ (Fin k)) h x

/-- The sum of the block projections composed with their inclusions is the
identity. -/
theorem sum_blockIncl_comp_blockProj :
    (∑ r : Fin n, (blockIncl k n r).comp (blockProj k n r))
      = (1 : PiLp 2 (fun _ : Fin n ↦ EuclideanSpace ℂ (Fin k)) →L[ℂ]
          PiLp 2 (fun _ : Fin n ↦ EuclideanSpace ℂ (Fin k))) := by
  refine ContinuousLinearMap.ext fun w ↦ ?_
  rw [sum_apply]
  refine ext_inner_left ℂ fun v ↦ ?_
  rw [inner_sum]
  have hterm : ∀ r : Fin n,
      ⟪v, ((blockIncl k n r).comp (blockProj k n r)) w⟫_ℂ
        = ⟪v r, w r⟫_ℂ := by
    intro r
    have h : ((blockIncl k n r).comp (blockProj k n r)) w
        = blockIncl k n r (w r) := rfl
    rw [h, inner_blockIncl_right]
  rw [Finset.sum_congr rfl fun r _ ↦ hterm r]
  have hone : ((1 : PiLp 2 (fun _ : Fin n ↦ EuclideanSpace ℂ (Fin k)) →L[ℂ]
      PiLp 2 (fun _ : Fin n ↦ EuclideanSpace ℂ (Fin k))) w) = w := rfl
  rw [hone]
  exact (inner_block_eq_sum v w).symm

/-- **A block matrix of operators as one operator** on the block Hilbert
space. -/
def blockOp
    (X : CStarMatrix (Fin n) (Fin n)
      (EuclideanSpace ℂ (Fin k) →L[ℂ] EuclideanSpace ℂ (Fin k))) :
    PiLp 2 (fun _ : Fin n ↦ EuclideanSpace ℂ (Fin k)) →L[ℂ]
      PiLp 2 (fun _ : Fin n ↦ EuclideanSpace ℂ (Fin k)) :=
  ∑ i : Fin n, ∑ j : Fin n,
    ((blockIncl k n i).comp ((X i j).comp (blockProj k n j)))

/-- The sesquilinear form of the block operator is the sum of the entry
forms. -/
theorem inner_blockOp
    (X : CStarMatrix (Fin n) (Fin n)
      (EuclideanSpace ℂ (Fin k) →L[ℂ] EuclideanSpace ℂ (Fin k)))
    (v w : PiLp 2 (fun _ : Fin n ↦ EuclideanSpace ℂ (Fin k))) :
    ⟪v, blockOp X w⟫_ℂ
      = ∑ i : Fin n, ∑ j : Fin n, ⟪v i, X i j (w j)⟫_ℂ := by
  rw [blockOp, sum_apply, inner_sum]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  rw [sum_apply, inner_sum]
  refine Finset.sum_congr rfl fun j _ ↦ ?_
  have h : (((blockIncl k n i).comp ((X i j).comp (blockProj k n j))) w)
      = blockIncl k n i ((X i j) (w j)) := rfl
  rw [h, inner_blockIncl_right]

/-- Entry recovery: compressing the block operator returns the entries. -/
theorem blockProj_comp_blockOp_comp_blockIncl
    (X : CStarMatrix (Fin n) (Fin n)
      (EuclideanSpace ℂ (Fin k) →L[ℂ] EuclideanSpace ℂ (Fin k)))
    (p q : Fin n) :
    (blockProj k n p).comp ((blockOp X).comp (blockIncl k n q))
      = X p q := by
  refine ContinuousLinearMap.ext fun x ↦ ?_
  refine ext_inner_left ℂ fun y ↦ ?_
  have h1 : (((blockProj k n p).comp
      ((blockOp X).comp (blockIncl k n q))) x)
      = blockProj k n p (blockOp X (blockIncl k n q x)) := rfl
  rw [h1]
  have h2 : ⟪y, blockProj k n p (blockOp X (blockIncl k n q x))⟫_ℂ
      = ⟪blockIncl k n p y, blockOp X (blockIncl k n q x)⟫_ℂ := by
    rw [inner_blockIncl_left]
    rfl
  rw [h2, inner_blockOp]
  have houter : ∑ i : Fin n, ∑ j : Fin n,
      ⟪blockIncl k n p y i, X i j (blockIncl k n q x j)⟫_ℂ
      = ∑ j : Fin n, ⟪y, X p j (blockIncl k n q x j)⟫_ℂ := by
    refine Finset.sum_eq_single p (fun i _ hi ↦ ?_)
      (fun h ↦ absurd (Finset.mem_univ p) h) |>.trans ?_
    · refine Finset.sum_eq_zero fun j _ ↦ ?_
      rw [blockIncl_coord_ne hi, inner_zero_left]
    · refine Finset.sum_congr rfl fun j _ ↦ ?_
      rw [blockIncl_coord_same]
  rw [houter]
  have hinner : ∑ j : Fin n, ⟪y, X p j (blockIncl k n q x j)⟫_ℂ
      = ⟪y, X p q (blockIncl k n q x q)⟫_ℂ := by
    refine Finset.sum_eq_single q (fun j _ hj ↦ ?_)
      (fun h ↦ absurd (Finset.mem_univ q) h)
    rw [blockIncl_coord_ne hj, map_zero, inner_zero_right]
  rw [hinner, blockIncl_coord_same]

/-- The block operator of the star matrix is the adjoint. -/
theorem blockOp_star
    (X : CStarMatrix (Fin n) (Fin n)
      (EuclideanSpace ℂ (Fin k) →L[ℂ] EuclideanSpace ℂ (Fin k))) :
    blockOp (star X) = ContinuousLinearMap.adjoint (blockOp X) := by
  refine ContinuousLinearMap.ext fun w ↦ ?_
  refine ext_inner_left ℂ fun v ↦ ?_
  rw [ContinuousLinearMap.adjoint_inner_right, inner_blockOp]
  have hterm : ∀ i j : Fin n,
      ⟪v i, (star X) i j (w j)⟫_ℂ = ⟪X j i (v i), w j⟫_ℂ := by
    intro i j
    have h : (star X) i j = star (X j i) := rfl
    rw [h, ContinuousLinearMap.star_eq_adjoint,
      ContinuousLinearMap.adjoint_inner_right]
  rw [Finset.sum_congr rfl fun i _ ↦
    Finset.sum_congr rfl fun j _ ↦ hterm i j]
  have hswap : ⟪blockOp X v, w⟫_ℂ
      = ∑ j : Fin n, ∑ i : Fin n, ⟪X j i (v i), w j⟫_ℂ := by
    rw [← inner_conj_symm, inner_blockOp, map_sum]
    refine Finset.sum_congr rfl fun j _ ↦ ?_
    rw [map_sum]
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    rw [inner_conj_symm]
  rw [hswap]
  exact Finset.sum_comm

/-- **The factorization bridge.**  A self-adjoint block matrix over `B(ℂᵏ)`
whose block operator has nonnegative quadratic form factors as `star P * P`
in `CStarMatrix`: the operator square root of the block operator, cut into
blocks by the compressions. -/
theorem exists_factor_of_blockOp_form_nonneg
    {X : CStarMatrix (Fin n) (Fin n)
      (EuclideanSpace ℂ (Fin k) →L[ℂ] EuclideanSpace ℂ (Fin k))}
    (hsa : star X = X)
    (hform : ∀ v : PiLp 2 (fun _ : Fin n ↦ EuclideanSpace ℂ (Fin k)),
      0 ≤ (⟪v, blockOp X v⟫_ℂ).re) :
    ∃ P : CStarMatrix (Fin n) (Fin n)
      (EuclideanSpace ℂ (Fin k) →L[ℂ] EuclideanSpace ℂ (Fin k)),
      X = star P * P := by
  classical
  have hadj : IsSelfAdjoint (blockOp X) := by
    rw [IsSelfAdjoint, ContinuousLinearMap.star_eq_adjoint, ← blockOp_star,
      hsa]
  have hpos : ContinuousLinearMap.IsPositive (blockOp X) := by
    refine ⟨(ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric).mp hadj,
      fun v ↦ ?_⟩
    have h := hform v
    rw [← inner_conj_symm, Complex.conj_re] at h
    exact h
  have h0 : (0 : PiLp 2 (fun _ : Fin n ↦ EuclideanSpace ℂ (Fin k)) →L[ℂ]
      PiLp 2 (fun _ : Fin n ↦ EuclideanSpace ℂ (Fin k))) ≤ blockOp X :=
    (ContinuousLinearMap.nonneg_iff_isPositive (blockOp X)).mpr hpos
  obtain ⟨S, hS⟩ := exists_star_mul_self_of_nonneg h0
  have hSS : ∀ w : PiLp 2 (fun _ : Fin n ↦ EuclideanSpace ℂ (Fin k)),
      ContinuousLinearMap.adjoint S (S w) = blockOp X w := by
    intro w
    have h := congrArg (fun T : PiLp 2
        (fun _ : Fin n ↦ EuclideanSpace ℂ (Fin k)) →L[ℂ]
        PiLp 2 (fun _ : Fin n ↦ EuclideanSpace ℂ (Fin k)) ↦ T w) hS
    rw [← ContinuousLinearMap.star_eq_adjoint]
    exact h.symm
  set Pm : CStarMatrix (Fin n) (Fin n)
      (EuclideanSpace ℂ (Fin k) →L[ℂ] EuclideanSpace ℂ (Fin k)) :=
    fun p q ↦ (blockProj k n p).comp (S.comp (blockIncl k n q))
    with hPm_def
  refine ⟨Pm, ?_⟩
  funext p q
  refine ContinuousLinearMap.ext fun x ↦ ?_
  refine ext_inner_left ℂ fun y ↦ ?_
  have hmul : (star Pm * Pm) p q = ∑ r : Fin n, (star Pm) p r * Pm r q :=
    Matrix.mul_apply
  have hchain : ⟪y, ((star Pm * Pm) p q) x⟫_ℂ = ⟪y, X p q x⟫_ℂ := by
    rw [hmul, sum_apply, inner_sum]
    have hterm : ∀ r : Fin n,
        ⟪y, ((star Pm) p r * Pm r q) x⟫_ℂ
          = ⟪(S (blockIncl k n p y)) r, (S (blockIncl k n q x)) r⟫_ℂ := by
      intro r
      have h1 : ((star Pm) p r * Pm r q) x
          = ContinuousLinearMap.adjoint (Pm r p) ((Pm r q) x) := rfl
      rw [h1, ContinuousLinearMap.adjoint_inner_right]
      have h2 : (Pm r p) y = (S (blockIncl k n p y)) r := rfl
      have h3 : (Pm r q) x = (S (blockIncl k n q x)) r := rfl
      rw [h2, h3]
    rw [Finset.sum_congr rfl fun r _ ↦ hterm r]
    rw [← inner_block_eq_sum]
    have h4 : ⟪S (blockIncl k n p y), S (blockIncl k n q x)⟫_ℂ
        = ⟪blockIncl k n p y,
            ContinuousLinearMap.adjoint S (S (blockIncl k n q x))⟫_ℂ :=
      (ContinuousLinearMap.adjoint_inner_right S _ _).symm
    rw [h4, hSS, inner_blockIncl_left]
    have h5 : (blockOp X (blockIncl k n q x)) p
        = blockProj k n p (blockOp X (blockIncl k n q x)) := rfl
    rw [h5]
    have h6 : blockProj k n p (blockOp X (blockIncl k n q x))
        = X p q x := by
      have h := congrArg
        (fun T : EuclideanSpace ℂ (Fin k) →L[ℂ]
          EuclideanSpace ℂ (Fin k) ↦ T x)
        (blockProj_comp_blockOp_comp_blockIncl X p q)
      exact h
    rw [h6]
  exact hchain.symm

end

end CStarExactness
end GroupApproximation
