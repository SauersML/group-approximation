import Mathlib.Algebra.Algebra.NonUnitalHom
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.GroupWithZero.Action.Units
import Mathlib.Algebra.Module.BigOperators
import Mathlib.Data.Finite.Prod
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Matrix.Basis
import Mathlib.Data.Set.Finite.Range

/-!
# Locally matricial algebras

`non_mf_groups_exist.tex`, sec:chain-core, the definition before lem:transient-matrices: an
algebra is *locally matricial* if every finite subset is contained in a finite product of full
matrix algebras over its coefficient field.

* `IsLocallyMatricialIn k S`: every finite subset of `S` lies in the range of an injective
  non-unital `k`-algebra hom `∏ₐ M_{h a}(k) → A` whose range lies in `S`.  The range is the
  printed subalgebra; its local identity is the image of `1`.
* `IsLocallyMatricial k A`: the case `S = univ`.
* `IsMatrixUnitFamily e`, `matrixUnitsHom`: matrix units in a non-unital algebra, indexed by
  finitely many square blocks, give a non-unital algebra hom from the product of matrix algebras,
  injective when the diagonal units are nonzero (`matrixUnitsHom_injective`).
* `isLocallyMatricialIn_of_forall_exists_family`: the criterion used for the transient ideal.
* `IsLocallyMatricialIn.exists_idempotent`, `.exists_finite`, `.exists_nonUnitalRingHom`: local
  identities, finiteness over a finite field, and the non-unital ring hom form.
* Model tests: `isLocallyMatricial_matrix` (positive), `not_isLocallyMatricialIn_squareZero`
  (negative).

The complete systems of matrix units of `Algebra/PeirceMatrixRing.lean` (`MatrixUnitSystem`) live
in a unital ring and sum to `1`; the families here need neither.
-/

namespace GroupApproximation
namespace ChainCore

/-- The printed definition, relative to a subset `S` of the ambient algebra: every finite subset
of `S` lies in a subalgebra `B ⊆ S` isomorphic to a finite product of full matrix algebras over
`k`; `B` is the range of the injective hom `φ`. -/
def IsLocallyMatricialIn (k : Type*) {A : Type*} [Field k] [NonUnitalRing A] [Module k A]
    (S : Set A) : Prop :=
  ∀ F : Finset A, (∀ x ∈ F, x ∈ S) → ∃ (m : ℕ) (h : Fin m → ℕ)
    (φ : (∀ a : Fin m, Matrix (Fin (h a)) (Fin (h a)) k) →ₙₐ[k] A),
    Function.Injective φ ∧ (∀ y, φ y ∈ S) ∧ ∀ x ∈ F, ∃ y, φ y = x

/-- A locally matricial algebra (the printed definition, `S = univ`). -/
def IsLocallyMatricial (k A : Type*) [Field k] [NonUnitalRing A] [Module k A] : Prop :=
  IsLocallyMatricialIn k (Set.univ : Set A)

section MatrixUnits

variable {k A : Type*} [Field k] [NonUnitalRing A] [Module k A] {m : ℕ} {h : Fin m → ℕ}

/-- Matrix units in a non-unital ring, indexed by finitely many square blocks: the `e a i j`
multiply like the matrix units of block `a`, and units of different blocks are orthogonal. -/
structure IsMatrixUnitFamily (e : ∀ a : Fin m, Fin (h a) → Fin (h a) → A) : Prop where
  mul_same : ∀ a (i j l : Fin (h a)), e a i j * e a j l = e a i l
  mul_of_ne : ∀ a (i j j' l : Fin (h a)), j ≠ j' → e a i j * e a j' l = 0
  mul_of_block_ne : ∀ a b, a ≠ b → ∀ (i j : Fin (h a)) (i' j' : Fin (h b)),
    e a i j * e b i' j' = 0

variable {e : ∀ a : Fin m, Fin (h a) → Fin (h a) → A}

/-- The image of one block, `X ↦ ∑ i j, X i j • e a i j`. -/
def matrixUnitsBlock (e : ∀ a : Fin m, Fin (h a) → Fin (h a) → A) (a : Fin m)
    (X : Matrix (Fin (h a)) (Fin (h a)) k) : A :=
  ∑ i, ∑ j, X i j • e a i j

theorem matrixUnitsBlock_mul [IsScalarTower k A A] (a : Fin m)
    (X : Matrix (Fin (h a)) (Fin (h a)) k) (B : A) :
    matrixUnitsBlock e a X * B = ∑ i, ∑ j, X i j • (e a i j * B) := by
  simp only [matrixUnitsBlock, Finset.sum_mul, smul_mul_assoc]

theorem IsMatrixUnitFamily.mul_matrixUnitsBlock [SMulCommClass k A A]
    (he : IsMatrixUnitFamily e) (a : Fin m) (i j : Fin (h a))
    (X : Matrix (Fin (h a)) (Fin (h a)) k) :
    e a i j * matrixUnitsBlock e a X = ∑ l, X j l • e a i l := by
  rw [matrixUnitsBlock, Finset.mul_sum]
  refine (Fintype.sum_eq_single j fun i' hi' => ?_).trans ?_
  · simp only [Finset.mul_sum, mul_smul_comm,
      fun l => he.mul_of_ne a i j i' l (Ne.symm hi'), smul_zero, Finset.sum_const_zero]
  · simp only [Finset.mul_sum, mul_smul_comm, he.mul_same]

theorem IsMatrixUnitFamily.mul_matrixUnitsBlock_of_ne [SMulCommClass k A A]
    (he : IsMatrixUnitFamily e) {a b : Fin m} (hab : a ≠ b) (i j : Fin (h a))
    (X : Matrix (Fin (h b)) (Fin (h b)) k) :
    e a i j * matrixUnitsBlock e b X = 0 := by
  simp only [matrixUnitsBlock, Finset.mul_sum, mul_smul_comm, he.mul_of_block_ne a b hab,
    smul_zero, Finset.sum_const_zero]

theorem IsMatrixUnitFamily.sum_smul_mul [IsScalarTower k A A] (he : IsMatrixUnitFamily e)
    (a : Fin m) (i j l : Fin (h a)) (x : Fin (h a) → k) :
    (∑ j', x j' • e a i j') * e a j l = x j • e a i l := by
  rw [Finset.sum_mul]
  refine (Fintype.sum_eq_single j fun j' hj' => ?_).trans ?_
  · simp only [smul_mul_assoc, he.mul_of_ne a i j' j l hj', smul_zero]
  · rw [smul_mul_assoc, he.mul_same]

theorem IsMatrixUnitFamily.matrixUnitsBlock_mul_matrixUnitsBlock [IsScalarTower k A A]
    [SMulCommClass k A A] (he : IsMatrixUnitFamily e) (a : Fin m)
    (X Y : Matrix (Fin (h a)) (Fin (h a)) k) :
    matrixUnitsBlock e a X * matrixUnitsBlock e a Y = matrixUnitsBlock e a (X * Y) := by
  rw [matrixUnitsBlock_mul]
  simp only [he.mul_matrixUnitsBlock, Finset.smul_sum, smul_smul]
  simp only [matrixUnitsBlock, Matrix.mul_apply, Finset.sum_smul]
  exact Finset.sum_congr rfl fun i _ => Finset.sum_comm

theorem IsMatrixUnitFamily.matrixUnitsBlock_mul_of_ne [SMulCommClass k A A]
    [IsScalarTower k A A] (he : IsMatrixUnitFamily e) {a b : Fin m} (hab : a ≠ b)
    (X : Matrix (Fin (h a)) (Fin (h a)) k) (Y : Matrix (Fin (h b)) (Fin (h b)) k) :
    matrixUnitsBlock e a X * matrixUnitsBlock e b Y = 0 := by
  simp only [matrixUnitsBlock_mul, he.mul_matrixUnitsBlock_of_ne hab, smul_zero,
    Finset.sum_const_zero]

theorem IsMatrixUnitFamily.ne_zero_of_diag (he : IsMatrixUnitFamily e)
    (hne : ∀ a i, e a i i ≠ 0) (a : Fin m) (i j : Fin (h a)) : e a i j ≠ 0 := by
  intro h0
  apply hne a i
  rw [← he.mul_same a i j i, h0, zero_mul]

variable (k) in
/-- The non-unital algebra hom `M ↦ ∑ a i j, M a i j • e a i j` of a matrix unit family. -/
noncomputable def matrixUnitsHom [IsScalarTower k A A] [SMulCommClass k A A]
    (he : IsMatrixUnitFamily e) :
    (∀ a : Fin m, Matrix (Fin (h a)) (Fin (h a)) k) →ₙₐ[k] A where
  toFun M := ∑ a, matrixUnitsBlock e a (M a)
  map_smul' c M := by
    simp only [matrixUnitsBlock, Pi.smul_apply, Matrix.smul_apply, smul_eq_mul, mul_smul,
      Finset.smul_sum, MonoidHom.id_apply]
  map_zero' := by
    simp only [matrixUnitsBlock, Pi.zero_apply, Matrix.zero_apply, zero_smul,
      Finset.sum_const_zero]
  map_add' M N := by
    simp only [matrixUnitsBlock, Pi.add_apply, Matrix.add_apply, add_smul, Finset.sum_add_distrib]
  map_mul' M N := by
    simp only [Pi.mul_apply, Finset.sum_mul_sum]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [Fintype.sum_eq_single a fun b hb => he.matrixUnitsBlock_mul_of_ne (Ne.symm hb) (M a) (N b)]
    exact (he.matrixUnitsBlock_mul_matrixUnitsBlock a (M a) (N a)).symm

variable (k) in
theorem matrixUnitsHom_apply [IsScalarTower k A A] [SMulCommClass k A A]
    (he : IsMatrixUnitFamily e) (M : ∀ a : Fin m, Matrix (Fin (h a)) (Fin (h a)) k) :
    matrixUnitsHom k he M = ∑ a, matrixUnitsBlock e a (M a) :=
  rfl

variable (k) in
/-- A matrix unit family with nonzero diagonal gives an injective hom: `e a i i * φ M * e a j j`
is `M a i j • e a i j`. -/
theorem matrixUnitsHom_injective [IsScalarTower k A A] [SMulCommClass k A A]
    (he : IsMatrixUnitFamily e) (hne : ∀ a i, e a i i ≠ 0) :
    Function.Injective (matrixUnitsHom k he) := by
  refine (injective_iff_map_eq_zero _).2 fun M hM => ?_
  ext a i j
  have key : e a i i * matrixUnitsHom k he M * e a j j = M a i j • e a i j := by
    rw [matrixUnitsHom_apply, Finset.mul_sum,
      Fintype.sum_eq_single a fun b hb => he.mul_matrixUnitsBlock_of_ne (Ne.symm hb) i i (M b),
      he.mul_matrixUnitsBlock, he.sum_smul_mul]
  rw [hM, mul_zero, zero_mul] at key
  show M a i j = 0
  by_contra hc
  exact he.ne_zero_of_diag hne a i j (by rw [← inv_smul_smul₀ hc (e a i j), ← key, smul_zero])

/-- The criterion: if `S` is closed under sums and `k`-scalars, and every finite subset of `S` is
spanned by a matrix unit family in `S` with nonzero diagonal, then `S` is locally matricial. -/
theorem isLocallyMatricialIn_of_forall_exists_family [IsScalarTower k A A] [SMulCommClass k A A]
    {S : Set A} (hzero : (0 : A) ∈ S) (hadd : ∀ x ∈ S, ∀ y ∈ S, x + y ∈ S)
    (hsmul : ∀ (c : k), ∀ x ∈ S, c • x ∈ S)
    (hfam : ∀ F : Finset A, (∀ x ∈ F, x ∈ S) → ∃ (m : ℕ) (h : Fin m → ℕ)
      (e : ∀ a : Fin m, Fin (h a) → Fin (h a) → A), IsMatrixUnitFamily e ∧
        (∀ a i, e a i i ≠ 0) ∧ (∀ a i j, e a i j ∈ S) ∧
        ∀ x ∈ F, ∃ c : ∀ a : Fin m, Matrix (Fin (h a)) (Fin (h a)) k,
          x = ∑ a, ∑ i, ∑ j, c a i j • e a i j) :
    IsLocallyMatricialIn k S := by
  intro F hF
  obtain ⟨m, h, e, he, hne, heS, hspan⟩ := hfam F hF
  refine ⟨m, h, matrixUnitsHom k he, matrixUnitsHom_injective k he hne, fun y => ?_,
    fun x hx => ?_⟩
  · simp only [matrixUnitsHom_apply, matrixUnitsBlock]
    refine Finset.sum_induction _ (· ∈ S) (fun x y hx hy => hadd x hx y hy) hzero fun a _ => ?_
    refine Finset.sum_induction _ (· ∈ S) (fun x y hx hy => hadd x hx y hy) hzero fun i _ => ?_
    refine Finset.sum_induction _ (· ∈ S) (fun x y hx hy => hadd x hx y hy) hzero fun j _ => ?_
    exact hsmul _ _ (heS a i j)
  · obtain ⟨c, rfl⟩ := hspan x hx
    exact ⟨c, rfl⟩

/-- Local identities: a finite subset of a locally matricial set has a two-sided idempotent unit
in the set (the image of `1`). -/
theorem IsLocallyMatricialIn.exists_idempotent {S : Set A} (hS : IsLocallyMatricialIn k S)
    (F : Finset A) (hF : ∀ x ∈ F, x ∈ S) :
    ∃ p ∈ S, p * p = p ∧ ∀ x ∈ F, p * x = x ∧ x * p = x := by
  obtain ⟨m, h, φ, -, hφS, hFφ⟩ := hS F hF
  refine ⟨φ 1, hφS 1, by rw [← map_mul φ, one_mul], fun x hx => ?_⟩
  obtain ⟨y, rfl⟩ := hFφ x hx
  exact ⟨by rw [← map_mul φ, one_mul], by rw [← map_mul φ, mul_one]⟩

/-- Over a finite field the printed subalgebra is finite. -/
theorem IsLocallyMatricialIn.exists_finite [Finite k] {S : Set A}
    (hS : IsLocallyMatricialIn k S) (F : Finset A) (hF : ∀ x ∈ F, x ∈ S) :
    ∃ (m : ℕ) (h : Fin m → ℕ) (φ : (∀ a : Fin m, Matrix (Fin (h a)) (Fin (h a)) k) →ₙₐ[k] A),
      Function.Injective φ ∧ (∀ y, φ y ∈ S) ∧ (∀ x ∈ F, ∃ y, φ y = x) ∧ (Set.range φ).Finite := by
  obtain ⟨m, h, φ, hinj, hφS, hFφ⟩ := hS F hF
  exact ⟨m, h, φ, hinj, hφS, hFφ, Set.finite_range φ⟩

/-- The same data with `φ` as a non-unital ring hom. -/
theorem IsLocallyMatricialIn.exists_nonUnitalRingHom {S : Set A}
    (hS : IsLocallyMatricialIn k S) (F : Finset A) (hF : ∀ x ∈ F, x ∈ S) :
    ∃ (m : ℕ) (h : Fin m → ℕ) (φ : (∀ a : Fin m, Matrix (Fin (h a)) (Fin (h a)) k) →ₙ+* A),
      Function.Injective φ ∧ (∀ y, φ y ∈ S) ∧ ∀ x ∈ F, ∃ y, φ y = x := by
  obtain ⟨m, h, φ, hinj, hφS, hFφ⟩ := hS F hF
  exact ⟨m, h, NonUnitalRingHomClass.toNonUnitalRingHom φ, hinj, hφS, hFφ⟩

end MatrixUnits

section ModelTests

variable (k : Type*) [Field k]

/-- Model test (positive): a full matrix algebra is locally matricial. -/
theorem isLocallyMatricial_matrix (n : ℕ) : IsLocallyMatricial k (Matrix (Fin n) (Fin n) k) := by
  refine isLocallyMatricialIn_of_forall_exists_family (Set.mem_univ _)
    (fun _ _ _ _ => Set.mem_univ _) (fun _ _ _ => Set.mem_univ _) fun F _ => ?_
  refine ⟨1, fun _ => n, fun _ i j => Matrix.single i j 1,
    ⟨fun _ i j l => ?_, fun _ i j j' l hj => ?_, fun a b hab => (hab (Subsingleton.elim a b)).elim⟩,
    fun _ i hi => ?_, fun _ _ _ => Set.mem_univ _, fun x _ => ⟨fun _ => x, ?_⟩⟩
  · simp
  · simp [hj]
  · simpa using congrFun (congrFun hi i) i
  · simp only [Fin.sum_univ_one, Matrix.smul_single, smul_eq_mul, mul_one]
    exact Matrix.matrix_eq_sum_single x

/-- Model test (negative): the square-zero line `k • E₀₁` is not locally matricial, since
`E₀₁` has no local identity inside it. -/
theorem not_isLocallyMatricialIn_squareZero :
    ¬ IsLocallyMatricialIn k
      {x : Matrix (Fin 2) (Fin 2) k | ∃ c : k, x = c • Matrix.single 0 1 1} := by
  intro hS
  obtain ⟨p, ⟨c, rfl⟩, -, hp⟩ := hS.exists_idempotent {Matrix.single 0 1 1}
    fun x hx => ⟨1, by rw [Finset.mem_singleton.1 hx, one_smul]⟩
  have hsq : (Matrix.single 0 1 1 * Matrix.single 0 1 1 : Matrix (Fin 2) (Fin 2) k) = 0 :=
    Matrix.single_mul_single_of_ne _ _ _ _ (by decide) _
  have h := (hp _ (Finset.mem_singleton_self _)).1
  rw [smul_mul_assoc, hsq, smul_zero] at h
  simpa using congrFun (congrFun h 0) 1

end ModelTests

end ChainCore
end GroupApproximation
