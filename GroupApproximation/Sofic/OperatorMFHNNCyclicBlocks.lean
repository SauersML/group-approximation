import GroupApproximation.Sofic.OperatorMFProduct
import GroupApproximation.Sofic.PermutationAdjointGap
import GroupApproximation.Sofic.KazhdanCornerModel
import GroupApproximation.Higman.HNNCentralizer
import GroupApproximation.Algebra.CountableInstances
import GroupApproximation.Sofic.LocallyFiniteMF

/-!
# Exact cyclic block models for whole-base HNN extensions

The operator norm sees the largest diagonal block.  Consequently the usual
Følner-stack proof for permutation or Hilbert--Schmidt models does not prove
operator-MF permanence for an arbitrary mapping torus: one bad wrap-around
block has full operator norm.  This file isolates the finite-dimensional
statement that *is* available without an external permanence theorem.

For a finite level set `I`, `fiberDiagonal A` places the matrix `A i` on the
`i`-th diagonal fibre of `I × Y`.  We prove directly that

* products and adjoints are computed fibrewise;
* unitary fibres give a unitary block matrix;
* a uniform fibrewise operator-norm bound is a bound for the whole matrix;
* every fibre norm is bounded by the whole norm; and
* conjugation by the permutation matrix of a level permutation transports the
  family by that permutation.

The last identity is the exact cyclic closing condition needed by a
whole-base HNN microstate.  No asymptotic or C-star-algebraic input occurs.

The final section records the first unconditional HNN permanence consequence:
when the stable letter centralizes the *whole* base, the HNN extension is the
direct product with `ℤ`, hence is operator-MF.  This is proved through explicit
homomorphisms and the repository's internal direct-product theorem.
-/

namespace GroupApproximation
namespace OperatorMFHNNCyclicBlocks

open Matrix
open scoped Matrix.Norms.L2Operator

noncomputable section

/-! ## Homogeneous finite block diagonals -/

variable {I Y : Type} [Fintype I] [DecidableEq I]
  [Fintype Y] [DecidableEq Y]

/-- The finite model consisting of `I` copies of `Y`. -/
abbrev fiberDiagonalModel (I Y : Type) [Fintype I] [DecidableEq I]
    [Fintype Y] [DecidableEq Y] : FiniteModel :=
  ⟨I × Y, inferInstance, inferInstance⟩

/-- The block diagonal with `i`-th diagonal block `A i`. -/
def fiberDiagonal (A : I → Matrix Y Y ℂ) : Matrix (I × Y) (I × Y) ℂ :=
  fun p q ↦ if p.1 = q.1 then A p.1 p.2 q.2 else 0

omit [Fintype I] [Fintype Y] [DecidableEq Y] in
@[simp] theorem fiberDiagonal_apply_same (A : I → Matrix Y Y ℂ)
    (i : I) (y z : Y) :
    fiberDiagonal A (i, y) (i, z) = A i y z := by
  simp [fiberDiagonal]

omit [Fintype I] [Fintype Y] [DecidableEq Y] in
@[simp] theorem fiberDiagonal_apply_ne (A : I → Matrix Y Y ℂ)
    {i j : I} (hij : i ≠ j) (y z : Y) :
    fiberDiagonal A (i, y) (j, z) = 0 := by
  simp [fiberDiagonal, hij]

omit [DecidableEq Y] in
/-- Multiplication of homogeneous block diagonals is fibrewise. -/
theorem fiberDiagonal_mul (A B : I → Matrix Y Y ℂ) :
    fiberDiagonal A * fiberDiagonal B = fiberDiagonal (fun i ↦ A i * B i) := by
  classical
  ext p q
  rcases p with ⟨i, y⟩
  rcases q with ⟨j, z⟩
  by_cases hij : i = j
  · subst j
    rw [Matrix.mul_apply, fiberDiagonal_apply_same]
    rw [Fintype.sum_prod_type]
    rw [Finset.sum_eq_single i]
    · simp only [fiberDiagonal_apply_same, Matrix.mul_apply]
    · intro k _ hki
      simp [fiberDiagonal, hki]
    · intro hi
      exact absurd (Finset.mem_univ i) hi
  · rw [Matrix.mul_apply, fiberDiagonal_apply_ne _ hij]
    rw [Fintype.sum_prod_type]
    apply Finset.sum_eq_zero
    intro k _
    by_cases hik : i = k
    · subst k
      simp [fiberDiagonal, hij]
    · simp [fiberDiagonal, hik]

omit [Fintype I] [Fintype Y] in
/-- The constant identity family gives the identity matrix. -/
theorem fiberDiagonal_one :
    fiberDiagonal (fun _ : I ↦ (1 : Matrix Y Y ℂ)) = 1 := by
  ext p q
  rcases p with ⟨i, y⟩
  rcases q with ⟨j, z⟩
  by_cases hij : i = j
  · subst j
    simp [fiberDiagonal, Matrix.one_apply]
  · have hpq : (i, y) ≠ (j, z) := fun h ↦ hij (congrArg Prod.fst h)
    simp [fiberDiagonal, hij, hpq]

omit [Fintype I] [Fintype Y] [DecidableEq Y] in
/-- Adjoints of homogeneous block diagonals are fibrewise. -/
theorem fiberDiagonal_conjTranspose (A : I → Matrix Y Y ℂ) :
    (fiberDiagonal A)ᴴ = fiberDiagonal (fun i ↦ (A i)ᴴ) := by
  ext p q
  rcases p with ⟨i, y⟩
  rcases q with ⟨j, z⟩
  by_cases hij : i = j
  · subst j
    simp [Matrix.conjTranspose_apply]
  · have hji : j ≠ i := Ne.symm hij
    simp [Matrix.conjTranspose_apply, fiberDiagonal, hij, hji]

/-- A homogeneous block diagonal of unitary matrices is unitary. -/
theorem fiberDiagonal_mem_unitaryGroup (A : I → Matrix Y Y ℂ)
    (hA : ∀ i, A i ∈ Matrix.unitaryGroup Y ℂ) :
    fiberDiagonal A ∈ Matrix.unitaryGroup (I × Y) ℂ := by
  have hAA : ∀ i, A i * (A i)ᴴ = 1 := by
    intro i
    have hi := Matrix.mem_unitaryGroup_iff.mp (hA i)
    rwa [Matrix.star_eq_conjTranspose] at hi
  rw [Matrix.mem_unitaryGroup_iff, Matrix.star_eq_conjTranspose,
    fiberDiagonal_conjTranspose, fiberDiagonal_mul]
  simpa only [hAA] using (fiberDiagonal_one (I := I) (Y := Y))

omit [DecidableEq Y] in
/-- Multiplication by a fibre diagonal acts independently on each fibre. -/
theorem fiberDiagonal_mulVec (A : I → Matrix Y Y ℂ)
    (x : I × Y → ℂ) (i : I) (y : Y) :
    (fiberDiagonal A *ᵥ x) (i, y) =
      (A i *ᵥ fun z ↦ x (i, z)) y := by
  classical
  rw [Matrix.mulVec, dotProduct, Fintype.sum_prod_type]
  rw [Finset.sum_eq_single i]
  · simp only [fiberDiagonal_apply_same, Matrix.mulVec, dotProduct]
  · intro j _ hji
    simp [fiberDiagonal, Ne.symm hji]
  · intro hi
    exact absurd (Finset.mem_univ i) hi

/-- A uniform bound on the fibre norms bounds the operator norm of the whole
block diagonal.  This is the operator-norm analogue of taking a maximum, proved
directly from the finite-dimensional `ℓ²` definition. -/
theorem norm_fiberDiagonal_le (A : I → Matrix Y Y ℂ) {C : ℝ}
    (hC : 0 ≤ C) (hA : ∀ i, ‖A i‖ ≤ C) : ‖fiberDiagonal A‖ ≤ C := by
  classical
  refine KazhdanCornerMatrices.l2_opNorm_le_of_sum_normSq_general
    (fiberDiagonal A) hC fun x ↦ ?_
  rw [Fintype.sum_prod_type]
  simp_rw [fiberDiagonal_mulVec]
  calc
    ∑ i : I, ∑ y : Y, Complex.normSq ((A i *ᵥ fun z ↦ x (i, z)) y)
        ≤ ∑ i : I, ‖A i‖ ^ 2 *
            ∑ z : Y, Complex.normSq (x (i, z)) :=
      Finset.sum_le_sum fun i _ ↦
        KazhdanCornerMatrices.sum_normSq_mulVec_le_general
          (A i) (fun z ↦ x (i, z))
    _ ≤ ∑ i : I, C ^ 2 * ∑ z : Y, Complex.normSq (x (i, z)) := by
      apply Finset.sum_le_sum
      intro i _
      apply mul_le_mul_of_nonneg_right
      · nlinarith [norm_nonneg (A i), hA i]
      · exact Finset.sum_nonneg fun z _ ↦ Complex.normSq_nonneg _
    _ = C ^ 2 * ∑ p : I × Y, Complex.normSq (x p) := by
      rw [Fintype.sum_prod_type, Finset.mul_sum]

/-- Every fibre norm is bounded by the norm of the whole block diagonal.  This
is the separation estimate used by a cyclic HNN microstate: separation in one
closed fibre survives in the assembled matrix. -/
theorem norm_fiber_le_norm_fiberDiagonal (A : I → Matrix Y Y ℂ) (i : I) :
    ‖A i‖ ≤ ‖fiberDiagonal A‖ := by
  classical
  refine KazhdanCornerMatrices.l2_opNorm_le_of_sum_normSq_general
    (A i) (norm_nonneg (fiberDiagonal A))
    fun x ↦ ?_
  let xhat : I × Y → ℂ := fun p ↦ if p.1 = i then x p.2 else 0
  have hval (y : Y) :
      (A i *ᵥ x) y = (fiberDiagonal A *ᵥ xhat) (i, y) := by
    rw [fiberDiagonal_mulVec]
    congr 1
    funext z
    simp [xhat]
  have hxhat :
      ∑ p : I × Y, Complex.normSq (xhat p) =
        ∑ y : Y, Complex.normSq (x y) := by
    rw [Fintype.sum_prod_type, Finset.sum_eq_single i]
    · simp [xhat]
    · intro j _ hji
      simp [xhat, hji]
    · intro hi
      exact absurd (Finset.mem_univ i) hi
  calc
    ∑ y : Y, Complex.normSq ((A i *ᵥ x) y) =
        ∑ y : Y, Complex.normSq ((fiberDiagonal A *ᵥ xhat) (i, y)) := by
      apply Finset.sum_congr rfl
      intro y _
      rw [hval]
    _ ≤ ∑ p : I × Y, Complex.normSq ((fiberDiagonal A *ᵥ xhat) p) := by
      rw [Fintype.sum_prod_type]
      let f : I → ℝ := fun j ↦
        ∑ y : Y, Complex.normSq ((fiberDiagonal A *ᵥ xhat) (j, y))
      change f i ≤ ∑ j : I, f j
      exact Finset.single_le_sum
        (f := f)
        (fun j _ ↦ Finset.sum_nonneg fun y _ ↦ Complex.normSq_nonneg _)
        (Finset.mem_univ i)
    _ ≤ ‖fiberDiagonal A‖ ^ 2 *
        ∑ p : I × Y, Complex.normSq (xhat p) :=
      sum_normSq_mulVec_le (fiberDiagonalModel I Y) (fiberDiagonal A) xhat
    _ = ‖fiberDiagonal A‖ ^ 2 *
        ∑ y : Y, Complex.normSq (x y) := by rw [hxhat]

/-! ## Exact level reindexing -/

/-- A permutation of the levels, acting trivially inside each fibre. -/
def levelPerm (e : Equiv.Perm I) : Equiv.Perm (I × Y) :=
  e.prodCongr (Equiv.refl Y)

omit [Fintype I] [DecidableEq I] [Fintype Y] [DecidableEq Y] in
@[simp] theorem levelPerm_apply (e : Equiv.Perm I) (i : I) (y : Y) :
    levelPerm e (i, y) = (e i, y) := rfl

/-- The explicit permutation matrix used to move the diagonal fibres. -/
def levelShift (e : Equiv.Perm I) : Matrix (I × Y) (I × Y) ℂ :=
  PermutationAdjointGap.permMatrix (levelPerm e)

/-- A level shift is unitary. -/
theorem levelShift_mem_unitaryGroup (e : Equiv.Perm I) :
    levelShift e ∈ Matrix.unitaryGroup (I × Y) ℂ := by
  have heq : levelShift (Y := Y) e =
      (levelPerm (Y := Y) e).permMatrix ℂ := by
    ext p q
    simp [levelShift, PermutationAdjointGap.permMatrix,
      Equiv.Perm.permMatrix, eq_comm]
  rw [heq]
  exact permMatrix_mem_unitaryGroup (fiberDiagonalModel I Y)
    (levelPerm (Y := Y) e)

/-- **Exact cyclic covariance.**  Conjugation by the level permutation sends
the block at `e i` to level `i`.  In particular, if a finite family of base
microstates closes cyclically, the stable-letter HNN relation has zero defect,
including at the wrap-around block. -/
theorem levelShift_conj_fiberDiagonal (e : Equiv.Perm I)
    (A : I → Matrix Y Y ℂ) :
    levelShift e * fiberDiagonal A * (levelShift e)ᴴ =
      fiberDiagonal (fun i ↦ A (e i)) := by
  ext p q
  rw [levelShift, PermutationAdjointGap.perm_conj_apply]
  rcases p with ⟨i, y⟩
  rcases q with ⟨j, z⟩
  by_cases hij : i = j
  · subst j
    simp [levelPerm]
  · have heij : e i ≠ e j := fun h ↦ hij (e.injective h)
    simp [levelPerm, fiberDiagonal, hij, heij]

/-! ## The central whole-base HNN extension -/

variable (G : Type) [Group G]

/-- The HNN extension in which the stable letter centralizes every base
element. -/
abbrev CentralMappingTorus : Type :=
  Higman.CentHNN (⊤ : Subgroup G)

/-- The map from the central whole-base HNN extension to `G × ℤ`. -/
def centralToProd : CentralMappingTorus G →* G × Multiplicative ℤ :=
  HNNExtension.lift (MonoidHom.inl G (Multiplicative ℤ))
    (1, Multiplicative.ofAdd 1) (by
      intro a
      apply Prod.ext <;> simp)

@[simp] theorem centralToProd_of (g : G) :
    centralToProd G
      ((HNNExtension.of : G →* CentralMappingTorus G) g) = (g, 1) := by
  rw [centralToProd, HNNExtension.lift_of]
  rfl

@[simp] theorem centralToProd_t :
    centralToProd G (HNNExtension.t : CentralMappingTorus G) =
      (1, Multiplicative.ofAdd 1) := by
  rw [centralToProd, HNNExtension.lift_t]

/-- The inverse map, written in normal form `g t^n`. -/
def centralFromProd : G × Multiplicative ℤ →* CentralMappingTorus G where
  toFun p := (HNNExtension.of : G →* CentralMappingTorus G) p.1 *
    (HNNExtension.t : CentralMappingTorus G) ^ p.2.toAdd
  map_one' := by simp
  map_mul' p q := by
    have hcomm : Commute
        ((HNNExtension.t : CentralMappingTorus G) ^ p.2.toAdd)
        ((HNNExtension.of : G →* CentralMappingTorus G) q.1) :=
      ((Higman.commute_t_of_iff (⊤ : Subgroup G) q.1).2
        (Subgroup.mem_top q.1)).zpow_left _
    change (HNNExtension.of : G →* CentralMappingTorus G) (p.1 * q.1) *
        (HNNExtension.t : CentralMappingTorus G) ^
          (p.2.toAdd + q.2.toAdd) =
      ((HNNExtension.of : G →* CentralMappingTorus G) p.1 *
          (HNNExtension.t : CentralMappingTorus G) ^ p.2.toAdd) *
        ((HNNExtension.of : G →* CentralMappingTorus G) q.1 *
          (HNNExtension.t : CentralMappingTorus G) ^ q.2.toAdd)
    rw [map_mul, _root_.zpow_add]
    calc
      (HNNExtension.of : G →* CentralMappingTorus G) p.1 *
            (HNNExtension.of : G →* CentralMappingTorus G) q.1 *
          ((HNNExtension.t : CentralMappingTorus G) ^ p.2.toAdd *
            (HNNExtension.t : CentralMappingTorus G) ^ q.2.toAdd) =
          (HNNExtension.of : G →* CentralMappingTorus G) p.1 *
            ((HNNExtension.of : G →* CentralMappingTorus G) q.1 *
              (HNNExtension.t : CentralMappingTorus G) ^ p.2.toAdd) *
                (HNNExtension.t : CentralMappingTorus G) ^ q.2.toAdd := by group
      _ = (HNNExtension.of : G →* CentralMappingTorus G) p.1 *
            ((HNNExtension.t : CentralMappingTorus G) ^ p.2.toAdd *
              (HNNExtension.of : G →* CentralMappingTorus G) q.1) *
                (HNNExtension.t : CentralMappingTorus G) ^ q.2.toAdd := by
          rw [hcomm.eq]
      _ = ((HNNExtension.of : G →* CentralMappingTorus G) p.1 *
              (HNNExtension.t : CentralMappingTorus G) ^ p.2.toAdd) *
            ((HNNExtension.of : G →* CentralMappingTorus G) q.1 *
              (HNNExtension.t : CentralMappingTorus G) ^ q.2.toAdd) := by group

@[simp] theorem centralFromProd_inl (g : G) :
    centralFromProd G (g, 1) =
      (HNNExtension.of : G →* CentralMappingTorus G) g := by
  simp [centralFromProd]

@[simp] theorem centralFromProd_stable :
    centralFromProd G (1, Multiplicative.ofAdd 1) =
      (HNNExtension.t : CentralMappingTorus G) := by
  simp [centralFromProd]

theorem centralFromProd_comp_centralToProd :
    (centralFromProd G).comp (centralToProd G) =
      MonoidHom.id (CentralMappingTorus G) := by
  apply HNNExtension.hom_ext
  · ext g
    simp
  · simp

theorem centralToProd_comp_centralFromProd :
    (centralToProd G).comp (centralFromProd G) =
      MonoidHom.id (G × Multiplicative ℤ) := by
  apply MonoidHom.ext
  intro p
  apply Prod.ext
  · simp [centralFromProd]
  · change (centralToProd G
      ((HNNExtension.of : G →* CentralMappingTorus G) p.1 *
        (HNNExtension.t : CentralMappingTorus G) ^ p.2.toAdd)).2 = p.2
    rw [map_mul, centralToProd_of, map_zpow, centralToProd_t]
    simp only [Prod.snd_mul, one_mul]
    change (Multiplicative.ofAdd (1 : ℤ)) ^ p.2.toAdd = p.2
    rw [← ofAdd_zsmul]
    simp

/-- The central whole-base HNN extension is literally the direct product of
the base with the infinite cyclic group. -/
def centralMappingTorusEquivProd :
    CentralMappingTorus G ≃* G × Multiplicative ℤ :=
  MonoidHom.toMulEquiv (centralToProd G) (centralFromProd G)
    (centralFromProd_comp_centralToProd G)
    (centralToProd_comp_centralFromProd G)

/-- **Unconditional operator-MF permanence for the central whole-base HNN
layer.**  This is an internal consequence of direct-product permanence and
the explicit equivalence above. -/
theorem isOperatorMF_centralMappingTorus [Countable G]
    (hG : IsOperatorMF G) : IsOperatorMF (CentralMappingTorus G) := by
  letI : Countable (Multiplicative ℤ) :=
    CountableInstances.multiplicativeIntCountable
  have hZ : IsOperatorMF (Multiplicative ℤ) :=
    isOperatorMF_of_isLEF isLEF_multiplicative_int
  have hprod : IsOperatorMF (G × Multiplicative ℤ) := hG.prod hZ
  exact hprod.comap (centralMappingTorusEquivProd G).toMonoidHom
    (centralMappingTorusEquivProd G).injective

end

end OperatorMFHNNCyclicBlocks
end GroupApproximation
