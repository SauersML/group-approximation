import GroupApproximation.Analysis.CStarChoiMap
import GroupApproximation.Analysis.LanceMatrixArveson
import GroupApproximation.Analysis.NormMatrixCorona
import GroupApproximation.Analysis.CStarUnitalCPContractive
import GroupApproximation.Meta.AxiomGuard

/-!
# Finite-dimensional positive lifting from the matrix corona

The Choi--Effros step in the Blackadar--Kirchberg characterization begins
with a finite-dimensional fact: a positive Choi matrix over a quotient lifts
to a positive Choi matrix over the numerator.  For the concrete quotient

`prod_n M_(d_n) -> (prod_n M_(d_n)) / (direct_sum_n M_(d_n))`,

this follows directly.  Factor the positive matrix in the quotient, lift the
finitely many entries of the factor, and take its Gram matrix upstairs.

This module proves that construction without postulating a lifting theorem.
It then normalizes the lift coordinatewise, proves that the normalization is
invisible in the corona, and obtains an exact completely positive contraction.
Obtaining maps back to the source algebra is the separate generalized-system
layer of the Blackadar--Kirchberg argument.
-/

namespace GroupApproximation
namespace BlackadarKirchberg

open Matrix
open Filter
open scoped InnerProductSpace
open scoped Matrix.Norms.L2Operator

universe u

noncomputable section

/-! ## Elementary closure properties of completely positive maps -/

variable {A : Type*} {B : Type*} [NonUnitalCStarAlgebra A]
  [NonUnitalCStarAlgebra B]

local instance matrixBlockCStarAlgebra (Z : Type*) [Fintype Z] [DecidableEq Z]
    [Nonempty Z] : CStarAlgebra (Matrix Z Z ℂ) where
  toNormedRing := inferInstance
  toStarRing := inferInstance
  toCompleteSpace := inferInstance
  toCStarRing := inferInstance
  toNormedAlgebra := inferInstance
  toStarModule := inferInstance

/-! ## The Stinespring bound with a nonunital constant -/

/-- A completely positive map into bounded operators has norm at most the
norm of the image of the unit.  This is the nonunital form of the
Stinespring estimate used below to certify the coordinate contractions. -/
theorem CStarExactness.IsCompletelyPositive.norm_apply_le_map_one
    {C : Type*} [CStarAlgebra C]
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [CompleteSpace H]
    {f : C →ₗ[ℂ] (H →L[ℂ] H)}
    (hf : CStarExactness.IsCompletelyPositive f) (c : C) :
    ‖f c‖ ≤ ‖f 1‖ * ‖c‖ := by
  have hV : ∀ x : H,
      ‖CStarExactness.stinespringV f hf x‖ ≤ Real.sqrt ‖f 1‖ * ‖x‖ := by
    intro x
    rw [CStarExactness.stinespringV_apply,
      UniformSpace.Completion.norm_coe]
    exact CStarExactness.norm_stinespringSingleOne_le f hf x
  have hpi : ‖CStarExactness.stinespringRepOp f hf c‖ ≤ ‖c‖ := by
    have h := NonUnitalStarAlgHom.norm_apply_le
      (CStarExactness.stinespringRepHom f hf) c
    rwa [CStarExactness.stinespringRepHom_apply] at h
  have key : ∀ x y : H, ‖inner ℂ x (f c y)‖ ≤
      (‖f 1‖ * ‖c‖) * ‖x‖ * ‖y‖ := by
    intro x y
    rw [← CStarExactness.inner_stinespringV_repOp f hf c x y]
    have hmid :
        ‖CStarExactness.stinespringRepOp f hf c
          (CStarExactness.stinespringV f hf y)‖ ≤
          ‖c‖ * (Real.sqrt ‖f 1‖ * ‖y‖) := by
      refine (ContinuousLinearMap.le_opNorm _ _).trans ?_
      exact mul_le_mul hpi (hV y) (norm_nonneg _) (norm_nonneg c)
    calc
      ‖inner ℂ (CStarExactness.stinespringV f hf x)
          (CStarExactness.stinespringRepOp f hf c
            (CStarExactness.stinespringV f hf y))‖
          ≤ ‖CStarExactness.stinespringV f hf x‖ *
              ‖CStarExactness.stinespringRepOp f hf c
                (CStarExactness.stinespringV f hf y)‖ :=
            norm_inner_le_norm _ _
      _ ≤ (Real.sqrt ‖f 1‖ * ‖x‖) *
              (‖c‖ * (Real.sqrt ‖f 1‖ * ‖y‖)) :=
            mul_le_mul (hV x) hmid (norm_nonneg _) (by positivity)
      _ = (Real.sqrt ‖f 1‖ * Real.sqrt ‖f 1‖) *
              ‖c‖ * ‖x‖ * ‖y‖ := by ring
      _ = (‖f 1‖ * ‖c‖) * ‖x‖ * ‖y‖ := by
            rw [Real.mul_self_sqrt (norm_nonneg (f 1))]
  refine ContinuousLinearMap.opNorm_le_bound _ (by positivity) fun y ↦ ?_
  rcases eq_or_ne ((f c) y) 0 with h0 | h0
  · rw [h0, norm_zero]
    positivity
  · have hself : ‖inner ℂ ((f c) y) ((f c) y)‖ = ‖(f c) y‖ ^ 2 := by
      rw [inner_self_eq_norm_sq_to_K]
      simp
    have hb := key ((f c) y) y
    rw [hself] at hb
    have hpos : 0 < ‖(f c) y‖ := norm_pos_iff.mpr h0
    have hdiv : ‖(f c) y‖ * ‖(f c) y‖ ≤
        ((‖f 1‖ * ‖c‖) * ‖y‖) * ‖(f c) y‖ := by
      calc
        ‖(f c) y‖ * ‖(f c) y‖ = ‖(f c) y‖ ^ 2 := (sq _).symm
        _ ≤ (‖f 1‖ * ‖c‖) * ‖(f c) y‖ * ‖y‖ := hb
        _ = ((‖f 1‖ * ‖c‖) * ‖y‖) * ‖(f c) y‖ := by ring
    exact le_of_mul_le_mul_right hdiv hpos

/-- The zero linear map is completely positive. -/
theorem isCompletelyPositive_zero :
    CStarExactness.IsCompletelyPositive (0 : A →ₗ[ℂ] B) := by
  intro n M _hM
  refine ⟨0, ?_⟩
  ext i j
  simp

/-! ## Choi maps on the repository's matrix blocks -/

/-- The row-Gram Choi map on an actual matrix block.  It is the Choi map on
`B(ℓ²(Fin k))`, precomposed with the canonical matrix/operator
star-algebra equivalence. -/
def matrixRowChoiMap {k : ℕ} (b : Fin k → B) :
    Matrix (Fin k) (Fin k) ℂ →ₗ[ℂ] B :=
  (CStarExactness.choiMap b).comp
    ((Matrix.toEuclideanCLM (n := Fin k) (𝕜 := ℂ)).toStarAlgHom.toNonUnitalStarAlgHom :
      Matrix (Fin k) (Fin k) ℂ →ₗ[ℂ]
        (EuclideanSpace ℂ (Fin k) →L[ℂ] EuclideanSpace ℂ (Fin k)))

/-- A row-Gram Choi map on a matrix block is completely positive. -/
theorem isCompletelyPositive_matrixRowChoiMap {k : ℕ} [Nonempty (Fin k)]
    (b : Fin k → B) :
    CStarExactness.IsCompletelyPositive (matrixRowChoiMap b) := by
  letI : PartialOrder B := CStarAlgebra.spectralOrder _
  letI : StarOrderedRing B := CStarAlgebra.spectralOrderedRing _
  have hrow := CStarExactness.isCompletelyPositive_choiMap b
  have hequiv := CStarExactness.isCompletelyPositive_of_starAlgHom
    (Matrix.toEuclideanCLM (n := Fin k) (𝕜 := ℂ)).toStarAlgHom.toNonUnitalStarAlgHom
  exact hrow.comp hequiv

@[simp] theorem matrixRowChoiMap_apply {k : ℕ} (b : Fin k → B)
    (T : Matrix (Fin k) (Fin k) ℂ) :
    matrixRowChoiMap b T =
      ∑ i : Fin k, ∑ j : Fin k, T i j • (star (b i) * b j) := by
  rw [matrixRowChoiMap, LinearMap.comp_apply, CStarExactness.choiMap_apply]
  refine Finset.sum_congr rfl fun i _ ↦ Finset.sum_congr rfl fun j _ ↦ ?_
  congr 1
  exact CStarExactness.inner_single_toEuclideanCLM T i j

/-- Reorder five finite sums by moving the middle index in front and then
swapping the two remaining index pairs. -/
theorem sum_swap_middle_and_pairs {ι κ σ ρ υ M : Type*}
    [Fintype ι] [Fintype κ] [Fintype σ] [Fintype ρ] [Fintype υ]
    [AddCommMonoid M] (F : ι → κ → σ → ρ → υ → M) :
    (∑ p : ι, ∑ q : κ, ∑ s : σ, ∑ r : ρ, ∑ u : υ, F p q s r u) =
      ∑ s : σ, ∑ r : ρ, ∑ u : υ, ∑ p : ι, ∑ q : κ, F p q s r u := by
  calc
    (∑ p : ι, ∑ q : κ, ∑ s : σ, ∑ r : ρ, ∑ u : υ, F p q s r u) =
        ∑ p : ι, ∑ s : σ, ∑ q : κ, ∑ r : ρ, ∑ u : υ, F p q s r u :=
      Finset.sum_congr rfl fun p _ ↦ Finset.sum_comm
    _ = ∑ s : σ, ∑ p : ι, ∑ q : κ, ∑ r : ρ, ∑ u : υ, F p q s r u :=
      Finset.sum_comm
    _ = ∑ s : σ, ∑ r : ρ, ∑ u : υ, ∑ p : ι, ∑ q : κ, F p q s r u := by
      refine Finset.sum_congr rfl fun s _ ↦ ?_
      exact CStarExactness.sum_swap_pairs (fun p q r u ↦ F p q s r u)

/-- The Choi map associated with a finite family of rows.  Its Choi matrix is
the Gram matrix `C_(p,q) = sum_s star (b s p) * b s q`. -/
def gramChoiMap {d k : ℕ} (b : Fin d → Fin k → B) :
    (EuclideanSpace ℂ (Fin k) →L[ℂ] EuclideanSpace ℂ (Fin k)) →ₗ[ℂ] B where
  toFun T := ∑ p : Fin k, ∑ q : Fin k,
    CStarExactness.euclideanEntryLM k p q T •
      (∑ s : Fin d, star (b s p) * b s q)
  map_add' S T := by
    simp [map_add, add_smul, Finset.sum_add_distrib]
  map_smul' z T := by
    simp [map_smul, smul_smul, Finset.smul_sum]

@[simp] theorem gramChoiMap_apply {d k : ℕ} (b : Fin d → Fin k → B)
    (T : EuclideanSpace ℂ (Fin k) →L[ℂ] EuclideanSpace ℂ (Fin k)) :
    gramChoiMap b T = ∑ p : Fin k, ∑ q : Fin k,
      CStarExactness.euclideanEntryLM k p q T •
        (∑ s : Fin d, star (b s p) * b s q) := rfl

/-- **A finite Gram-family Choi map is completely positive.**

This is the general Choi computation needed for quotient lifting.  Unlike a
closure-under-sums shortcut, the proof produces the positive factor at every
matrix level explicitly. -/
theorem isCompletelyPositive_gramChoiMap {d k : ℕ}
    (b : Fin d → Fin k → B) :
    CStarExactness.IsCompletelyPositive (gramChoiMap b) := by
  classical
  letI : PartialOrder B := CStarAlgebra.spectralOrder _
  letI : StarOrderedRing B := CStarAlgebra.spectralOrderedRing _
  refine CStarExactness.isCompletelyPositive_of_map_nonneg _ fun n Y hY ↦ ?_
  rcases Nat.eq_zero_or_pos n with hn | hn
  · subst hn
    refine le_of_eq ?_
    funext i
    exact i.elim0
  · haveI : NeZero n := ⟨by omega⟩
    obtain ⟨Z, hZ⟩ := CStarExactness.exists_star_mul_self_of_nonneg hY
    set w : Fin d → Fin n → Fin k → Fin n → B := fun s r u i ↦
      ∑ p : Fin k, CStarExactness.euclideanEntryLM k u p (Z r i) • b s p
      with hw
    have hentry : ∀ i j : Fin n, (Y.map ⇑(gramChoiMap b)) i j =
        ∑ s : Fin d, ∑ r : Fin n, ∑ u : Fin k,
          star (w s r u i) * w s r u j := by
      intro i j
      have hYij : Y i j = ∑ r : Fin n, star (Z r i) * Z r j := by
        rw [hZ, CStarExactness.cstarMatrix_mul_apply]
        exact Finset.sum_congr rfl fun r _ ↦ by
          rw [CStarExactness.cstarMatrix_star_apply]
      have hmapentry : (Y.map ⇑(gramChoiMap b)) i j = gramChoiMap b (Y i j) := rfl
      have hcoef : ∀ p q : Fin k,
          CStarExactness.euclideanEntryLM k p q (Y i j) =
            ∑ r : Fin n, ∑ u : Fin k,
              star (CStarExactness.euclideanEntryLM k u p (Z r i)) *
                CStarExactness.euclideanEntryLM k u q (Z r j) := by
        intro p q
        rw [hYij, map_sum]
        refine Finset.sum_congr rfl fun r _ ↦ ?_
        rw [CStarExactness.euclideanEntry_mul]
        exact Finset.sum_congr rfl fun u _ ↦ by
          rw [CStarExactness.euclideanEntry_star]
      have hleft : (Y.map ⇑(gramChoiMap b)) i j =
          ∑ p : Fin k, ∑ q : Fin k, ∑ s : Fin d, ∑ r : Fin n,
            ∑ u : Fin k,
              (star (CStarExactness.euclideanEntryLM k u p (Z r i)) *
                CStarExactness.euclideanEntryLM k u q (Z r j)) •
                  (star (b s p) * b s q) := by
        rw [hmapentry, gramChoiMap_apply]
        refine Finset.sum_congr rfl fun p _ ↦ Finset.sum_congr rfl fun q _ ↦ ?_
        rw [Finset.smul_sum, hcoef p q]
        refine Finset.sum_congr rfl fun s _ ↦ ?_
        rw [Finset.sum_smul]
        exact Finset.sum_congr rfl fun r _ ↦ Finset.sum_smul
      have hright : ∀ s : Fin d, ∀ r : Fin n, ∀ u : Fin k,
          star (w s r u i) * w s r u j =
            ∑ p : Fin k, ∑ q : Fin k,
              (star (CStarExactness.euclideanEntryLM k u p (Z r i)) *
                CStarExactness.euclideanEntryLM k u q (Z r j)) •
                  (star (b s p) * b s q) := by
        intro s r u
        rw [hw]
        exact CStarExactness.star_combination_mul_combination (b s) _ _
      rw [hleft, sum_swap_middle_and_pairs]
      exact (Finset.sum_congr rfl fun s _ ↦
        Finset.sum_congr rfl fun r _ ↦
          Finset.sum_congr rfl fun u _ ↦ hright s r u).symm
    have hsum : Y.map ⇑(gramChoiMap b) =
        ∑ s : Fin d, ∑ r : Fin n, ∑ u : Fin k,
          CStarMatrix.ofMatrix
            (Matrix.of fun i j ↦ star (w s r u i) * w s r u j) := by
      show (Y.map ⇑(gramChoiMap b) : Matrix (Fin n) (Fin n) B) =
        ∑ s : Fin d, ∑ r : Fin n, ∑ u : Fin k,
          ((Matrix.of fun i j ↦ star (w s r u i) * w s r u j) :
            Matrix (Fin n) (Fin n) B)
      funext i j
      rw [hentry i j]
      simp only [Matrix.sum_apply, Matrix.of_apply]
    rw [hsum]
    exact Finset.sum_nonneg fun s _ ↦ Finset.sum_nonneg fun r _ ↦
      Finset.sum_nonneg fun u _ ↦ CStarExactness.rankOne_nonneg (w s r u)

/-- The same finite Gram-family Choi map, on the concrete matrix block. -/
def matrixGramChoiMap {d k : ℕ} (b : Fin d → Fin k → B) :
    Matrix (Fin k) (Fin k) ℂ →ₗ[ℂ] B :=
  (gramChoiMap b).comp
    ((Matrix.toEuclideanCLM (n := Fin k) (𝕜 := ℂ)).toStarAlgHom.toNonUnitalStarAlgHom :
      Matrix (Fin k) (Fin k) ℂ →ₗ[ℂ]
        (EuclideanSpace ℂ (Fin k) →L[ℂ] EuclideanSpace ℂ (Fin k)))

/-- A finite Gram-family Choi map on a positive-dimensional matrix block is
completely positive. -/
theorem isCompletelyPositive_matrixGramChoiMap {d k : ℕ} [Nonempty (Fin k)]
    (b : Fin d → Fin k → B) :
    CStarExactness.IsCompletelyPositive (matrixGramChoiMap b) := by
  have hgram := isCompletelyPositive_gramChoiMap b
  have hequiv := CStarExactness.isCompletelyPositive_of_starAlgHom
    (Matrix.toEuclideanCLM (n := Fin k) (𝕜 := ℂ)).toStarAlgHom.toNonUnitalStarAlgHom
  exact hgram.comp hequiv

@[simp] theorem matrixGramChoiMap_apply {d k : ℕ}
    (b : Fin d → Fin k → B) (T : Matrix (Fin k) (Fin k) ℂ) :
    matrixGramChoiMap b T = ∑ p : Fin k, ∑ q : Fin k, T p q •
      (∑ s : Fin d, star (b s p) * b s q) := by
  rw [matrixGramChoiMap, LinearMap.comp_apply, gramChoiMap_apply]
  refine Finset.sum_congr rfl fun p _ ↦ Finset.sum_congr rfl fun q _ ↦ ?_
  congr 1
  exact CStarExactness.inner_single_toEuclideanCLM T p q

variable (X : ℕ → Type u) [∀ n, Fintype (X n)] [∀ n, DecidableEq (X n)]
  [∀ n, Nonempty (X n)]

local instance boundedMatrixSequenceCStarAlgebra :
    CStarAlgebra (BoundedMatrixSequence X) where
  toNormedRing := inferInstance
  toStarRing := inferInstance
  toCompleteSpace := inferInstance
  toCStarRing := inferInstance
  toNormedAlgebra := inferInstance
  toStarModule := inferInstance

/-! ## Positive coordinate rescaling -/

/-- Coordinatewise multiplication by a nonnegative real scalar bounded by
one, as a linear map on the bounded matrix product. -/
def coordinateScale (s : ℕ → ℝ) (hs0 : ∀ n, 0 ≤ s n)
    (hs1 : ∀ n, s n ≤ 1) :
    BoundedMatrixSequence X →ₗ[ℂ] BoundedMatrixSequence X where
  toFun a := ⟨fun n ↦ (s n : ℂ) • a n, (lp.memℓp a).mono' fun n ↦ by
    rw [norm_smul]
    have hsNorm : ‖(s n : ℂ)‖ = s n := by
      simpa only [Complex.norm_real] using Real.norm_of_nonneg (hs0 n)
    rw [hsNorm]
    simpa only [one_mul] using
      mul_le_mul_of_nonneg_right (hs1 n) (norm_nonneg (a n))⟩
  map_add' a b := by
    refine lp.ext (funext fun n ↦ ?_)
    simp
  map_smul' z a := by
    apply lp.ext
    funext n
    simpa only [lp.coeFn_smul, Pi.smul_apply, smul_smul,
      RingHom.id_apply] using
      congrArg (fun c : ℂ ↦ c • a n) (mul_comm (s n : ℂ) z)

@[simp] theorem coordinateScale_apply (s : ℕ → ℝ) (hs0 : ∀ n, 0 ≤ s n)
    (hs1 : ∀ n, s n ≤ 1) (a : BoundedMatrixSequence X) (n : ℕ) :
    coordinateScale X s hs0 hs1 a n = (s n : ℂ) • a n := rfl

/-- Positive coordinate rescaling preserves complete positivity. -/
theorem isCompletelyPositive_coordinateScale (s : ℕ → ℝ)
    (hs0 : ∀ n, 0 ≤ s n) (hs1 : ∀ n, s n ≤ 1) :
    CStarExactness.IsCompletelyPositive (coordinateScale X s hs0 hs1) := by
  intro m M hM
  obtain ⟨P, hP⟩ := hM
  let Q : CStarMatrix (Fin m) (Fin m) (BoundedMatrixSequence X) :=
    CStarMatrix.ofMatrix (Matrix.of fun i j ↦
      ⟨fun n ↦ ((Real.sqrt (s n) : ℝ) : ℂ) • P i j n,
        (lp.memℓp (P i j)).mono' fun n ↦ by
          rw [norm_smul]
          have hsqrt : Real.sqrt (s n) ≤ 1 := by
            rw [← Real.sqrt_one]
            exact Real.sqrt_le_sqrt (hs1 n)
          have hsqrtNorm : ‖((Real.sqrt (s n) : ℝ) : ℂ)‖ =
              Real.sqrt (s n) := by
            simpa only [Complex.norm_real] using
              Real.norm_of_nonneg (Real.sqrt_nonneg (s n))
          rw [hsqrtNorm]
          simpa only [one_mul] using
            mul_le_mul_of_nonneg_right hsqrt (norm_nonneg (P i j n))⟩)
  refine ⟨Q, ?_⟩
  show M.map ⇑(coordinateScale X s hs0 hs1) = star Q * Q
  funext i j
  apply lp.ext
  funext n
  have hPentry : M i j = ∑ r : Fin m, star (P r i) * P r j := by
    calc
      M i j = (star P * P) i j := by
        exact congrArg (fun T : CStarMatrix (Fin m) (Fin m)
          (BoundedMatrixSequence X) ↦ T i j) hP
      _ = ∑ r : Fin m, star (P r i) * P r j := by
        rw [CStarExactness.cstarMatrix_mul_apply]
        exact Finset.sum_congr rfl fun r _ ↦ by
          rw [CStarExactness.cstarMatrix_star_apply]
  change coordinateScale X s hs0 hs1 (M i j) n = (star Q * Q) i j n
  rw [coordinateScale_apply, CStarExactness.cstarMatrix_mul_apply]
  simp_rw [CStarExactness.cstarMatrix_star_apply]
  let evalAt : BoundedMatrixSequence X →+
      Matrix (X n) (X n) ℂ :=
    { toFun := fun a ↦ a n
      map_zero' := rfl
      map_add' := fun _ _ ↦ rfl }
  change (s n : ℂ) • M i j n =
    evalAt (∑ r : Fin m, star (Q r i) * Q r j)
  rw [map_sum]
  change (s n : ℂ) • M i j n =
    ∑ r : Fin m,
      star (((Real.sqrt (s n) : ℝ) : ℂ) • P r i n) *
        (((Real.sqrt (s n) : ℝ) : ℂ) • P r j n)
  have hPcoord : M i j n =
      ∑ r : Fin m, star (P r i n) * P r j n := by
    calc
      M i j n = evalAt (∑ r : Fin m, star (P r i) * P r j) :=
        congrArg evalAt hPentry
      _ = ∑ r : Fin m, evalAt (star (P r i) * P r j) := by
        rw [map_sum]
      _ = ∑ r : Fin m, star (P r i n) * P r j n := by
        refine Finset.sum_congr rfl fun r _ ↦ ?_
        change (star (P r i) * P r j) n =
          star (P r i n) * P r j n
        rfl
  rw [hPcoord, Finset.smul_sum]
  refine Finset.sum_congr rfl fun r _ ↦ ?_
  have hsqrt : Real.sqrt (s n) * Real.sqrt (s n) = s n := by
    rw [Real.mul_self_sqrt (hs0 n)]
  have hsqrtC : ((Real.sqrt (s n) : ℂ) * (Real.sqrt (s n) : ℂ)) =
      (s n : ℂ) := by
    rw [← Complex.ofReal_mul, hsqrt]
  have hstarSqrt : star (Real.sqrt (s n) : ℂ) =
      (Real.sqrt (s n) : ℂ) := by
    rw [Complex.star_def, Complex.conj_ofReal]
  rw [star_smul, hstarSqrt, smul_mul_assoc, mul_smul_comm, smul_smul,
    hsqrtC]

/-! ## Coordinate contractions and corona-invisible normalization -/

/-- Evaluation at one coordinate of the bounded matrix product. -/
def coordinateEvaluation (n : ℕ) :
    BoundedMatrixSequence X →ₗ[ℂ] Matrix (X n) (X n) ℂ where
  toFun a := a n
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

@[simp] theorem coordinateEvaluation_apply (n : ℕ)
    (a : BoundedMatrixSequence X) : coordinateEvaluation X n a = a n := rfl

/-- Coordinate evaluation is completely positive. -/
theorem isCompletelyPositive_coordinateEvaluation (n : ℕ) :
    CStarExactness.IsCompletelyPositive (coordinateEvaluation X n) := by
  intro m M hM
  obtain ⟨P, hP⟩ := hM
  let Q : CStarMatrix (Fin m) (Fin m) (Matrix (X n) (X n) ℂ) :=
    CStarMatrix.ofMatrix (Matrix.of fun i j ↦ P i j n)
  refine ⟨Q, ?_⟩
  funext i j
  have hPentry : M i j = ∑ r : Fin m, star (P r i) * P r j := by
    calc
      M i j = (star P * P) i j := congrArg
        (fun T : CStarMatrix (Fin m) (Fin m)
          (BoundedMatrixSequence X) ↦ T i j) hP
      _ = ∑ r : Fin m, star (P r i) * P r j := by
        rw [CStarExactness.cstarMatrix_mul_apply]
        exact Finset.sum_congr rfl fun r _ ↦ by
          rw [CStarExactness.cstarMatrix_star_apply]
  rw [CStarExactness.cstarMatrix_mul_apply]
  simp_rw [CStarExactness.cstarMatrix_star_apply]
  change M i j n = ∑ r : Fin m, star (P r i n) * P r j n
  calc
    M i j n = (∑ r : Fin m, star (P r i) * P r j) n :=
      congrArg (fun a : BoundedMatrixSequence X ↦ a n) hPentry
    _ = ∑ r : Fin m, star (P r i n) * P r j n := by
      let evalAt : BoundedMatrixSequence X →+ Matrix (X n) (X n) ℂ :=
        { toFun := fun a ↦ a n
          map_zero' := rfl
          map_add' := fun _ _ ↦ rfl }
      change evalAt (∑ r : Fin m, star (P r i) * P r j) = _
      rw [map_sum]
      exact Finset.sum_congr rfl fun r _ ↦ by
        change (star (P r i) * P r j) n =
          star (P r i n) * P r j n
        rfl

/-- The Stinespring norm estimate for a completely positive map between
concrete full matrix algebras. -/
theorem CStarExactness.IsCompletelyPositive.matrix_norm_apply_le_map_one
    {C : Type*} [CStarAlgebra C]
    {Y : Type*} [Fintype Y] [DecidableEq Y] [Nonempty Y]
    (f : C →ₗ[ℂ] Matrix Y Y ℂ)
    (hf : CStarExactness.IsCompletelyPositive f)
    (c : C) : ‖f c‖ ≤ ‖f 1‖ * ‖c‖ := by
  let e : Matrix Y Y ℂ →ₗ[ℂ]
      (EuclideanSpace ℂ Y →L[ℂ] EuclideanSpace ℂ Y) :=
    (Matrix.toEuclideanCLM (n := Y) (𝕜 := ℂ)).toStarAlgHom.toNonUnitalStarAlgHom
  let g : C →ₗ[ℂ] (EuclideanSpace ℂ Y →L[ℂ] EuclideanSpace ℂ Y) :=
    e.comp f
  have he : CStarExactness.IsCompletelyPositive e :=
    CStarExactness.isCompletelyPositive_of_starAlgHom
      (Matrix.toEuclideanCLM (n := Y) (𝕜 := ℂ)).toStarAlgHom.toNonUnitalStarAlgHom
  have hg : CStarExactness.IsCompletelyPositive g := he.comp hf
  have hbound : ‖g c‖ ≤ ‖g 1‖ * ‖c‖ :=
    CStarExactness.IsCompletelyPositive.norm_apply_le_map_one hg c
  calc
    ‖f c‖ = ‖Matrix.toEuclideanCLM (n := Y) (𝕜 := ℂ) (f c)‖ :=
      (Matrix.l2_opNorm_toEuclideanCLM (f c)).symm
    _ = ‖g c‖ := rfl
    _ ≤ ‖g 1‖ * ‖c‖ := hbound
    _ = ‖Matrix.toEuclideanCLM (n := Y) (𝕜 := ℂ) (f 1)‖ * ‖c‖ := rfl
    _ = ‖f 1‖ * ‖c‖ := by
      rw [Matrix.l2_opNorm_toEuclideanCLM]

/-- The scalar that normalizes the image of the unit in each coordinate. -/
def unitNormalizationScale {C : Type*} [AddCommMonoid C] [Module ℂ C]
    [One C] (lift : C →ₗ[ℂ] BoundedMatrixSequence X)
    (n : ℕ) : ℝ := (max 1 ‖lift 1 n‖)⁻¹

theorem unitNormalizationScale_nonneg
    {C : Type*} [AddCommMonoid C] [Module ℂ C] [One C]
    (lift : C →ₗ[ℂ] BoundedMatrixSequence X)
    (n : ℕ) : 0 ≤ unitNormalizationScale X lift n := by
  exact inv_nonneg.mpr (le_trans (by norm_num) (le_max_left _ _))

theorem unitNormalizationScale_le_one
    {C : Type*} [AddCommMonoid C] [Module ℂ C] [One C]
    (lift : C →ₗ[ℂ] BoundedMatrixSequence X)
    (n : ℕ) : unitNormalizationScale X lift n ≤ 1 := by
  apply (inv_le_one₀ (lt_of_lt_of_le (by norm_num) (le_max_left 1 ‖lift 1 n‖))).2
  exact le_max_left _ _

/-- Coordinate normalization of a matrix-valued lift. -/
def normalizeMatrixLift
    {C : Type*} [AddCommMonoid C] [Module ℂ C] [One C]
    (lift : C →ₗ[ℂ] BoundedMatrixSequence X) :
    C →ₗ[ℂ] BoundedMatrixSequence X :=
  (coordinateScale X (unitNormalizationScale X lift)
    (unitNormalizationScale_nonneg X lift)
    (unitNormalizationScale_le_one X lift)).comp lift

/-- A completely positive matrix lift remains completely positive after
coordinate normalization. -/
theorem isCompletelyPositive_normalizeMatrixLift
    {C : Type*} [CStarAlgebra C]
    (lift : C →ₗ[ℂ] BoundedMatrixSequence X)
    (hlift : CStarExactness.IsCompletelyPositive lift) :
    CStarExactness.IsCompletelyPositive (normalizeMatrixLift X lift) := by
  have hscale := isCompletelyPositive_coordinateScale X
    (unitNormalizationScale X lift)
    (unitNormalizationScale_nonneg X lift)
    (unitNormalizationScale_le_one X lift)
  intro m M hM
  obtain ⟨P, hP⟩ := hlift m M hM
  obtain ⟨Q, hQ⟩ := hscale m (M.map ⇑lift) ⟨P, hP⟩
  refine ⟨Q, ?_⟩
  have hmap : M.map ⇑(normalizeMatrixLift X lift) =
      (M.map ⇑lift).map ⇑(coordinateScale X
        (unitNormalizationScale X lift)
        (unitNormalizationScale_nonneg X lift)
        (unitNormalizationScale_le_one X lift)) := by
    ext i j
    rfl
  rw [hmap]
  exact hQ

/-- Every coordinate of the normalized lift is contractive. -/
theorem normalizeMatrixLift_coordinate_norm_le
    {C : Type*} [CStarAlgebra C]
    (lift : C →ₗ[ℂ] BoundedMatrixSequence X)
    (hlift : CStarExactness.IsCompletelyPositive lift)
    (c : C) (n : ℕ) :
    ‖normalizeMatrixLift X lift c n‖ ≤ ‖c‖ := by
  let f : C →ₗ[ℂ] Matrix (X n) (X n) ℂ :=
    (coordinateEvaluation X n).comp (normalizeMatrixLift X lift)
  have hf : CStarExactness.IsCompletelyPositive f :=
    CStarExactness.IsCompletelyPositive.comp
      (isCompletelyPositive_coordinateEvaluation X n)
      (isCompletelyPositive_normalizeMatrixLift X lift hlift)
  have hmap :=
    CStarExactness.IsCompletelyPositive.matrix_norm_apply_le_map_one f hf c
  have hmaxpos : 0 < max 1 ‖lift 1 n‖ :=
    lt_of_lt_of_le (by norm_num) (le_max_left _ _)
  have hone : ‖f 1‖ ≤ 1 := by
    change ‖(unitNormalizationScale X lift n : ℂ) • lift 1 n‖ ≤ 1
    rw [norm_smul, Complex.norm_real,
      Real.norm_of_nonneg (unitNormalizationScale_nonneg X lift n)]
    calc
      unitNormalizationScale X lift n * ‖lift 1 n‖ ≤
          unitNormalizationScale X lift n * max 1 ‖lift 1 n‖ :=
        mul_le_mul_of_nonneg_left (le_max_right _ _)
          (unitNormalizationScale_nonneg X lift n)
      _ = 1 := inv_mul_cancel₀ hmaxpos.ne'
  change ‖normalizeMatrixLift X lift c n‖ ≤ ‖c‖
  exact hmap.trans (by simpa only [one_mul] using
    mul_le_mul_of_nonneg_right hone (norm_nonneg c))

/-- The normalized lift is a contraction in the product norm. -/
theorem normalizeMatrixLift_norm_le
    {C : Type*} [CStarAlgebra C]
    (lift : C →ₗ[ℂ] BoundedMatrixSequence X)
    (hlift : CStarExactness.IsCompletelyPositive lift)
    (c : C) : ‖normalizeMatrixLift X lift c‖ ≤ ‖c‖ := by
  rw [boundedMatrixSequence_norm_eq_ciSup]
  exact ciSup_le fun n ↦ normalizeMatrixLift_coordinate_norm_le X lift hlift c n

/-- If the corona class of a bounded sequence has norm at most one, then the
coordinate norms, truncated below by one, converge to one. -/
theorem tendsto_max_one_coord_norm_of_corona_norm_le_one
    (a : BoundedMatrixSequence X)
    (ha : ‖normMatrixCStarCoronaMk X a‖ ≤ 1) :
    Tendsto (fun n ↦ max 1 ‖a n‖) atTop (nhds 1) := by
  have hb : IsBoundedUnder (· ≤ ·) atTop (fun coord : ℕ ↦ ‖a coord‖) :=
    ⟨‖a‖, show ∀ᶠ coord : ℕ in atTop, ‖a coord‖ ≤ ‖a‖ from
      Eventually.of_forall fun coord : ℕ ↦
        boundedMatrixSequence_coord_norm_le X a coord⟩
  have hlimCof : Filter.limsup (fun coord : ℕ ↦ ‖a coord‖) cofinite ≤ 1 := by
    rw [← norm_filterMatrixCorona_mk_eq_limsup X cofinite]
    exact ha
  have hlim : Filter.limsup (fun coord : ℕ ↦ ‖a coord‖) atTop ≤ 1 := by
    simpa only [Nat.cofinite_eq_atTop] using hlimCof
  rw [Metric.tendsto_nhds]
  intro ε hε
  have hev : ∀ᶠ coord : ℕ in atTop, ‖a coord‖ < 1 + ε :=
    Filter.eventually_lt_of_limsup_lt
      (hlim.trans_lt (lt_add_of_pos_right 1 hε)) hb
  filter_upwards [hev] with coord hcoord
  rw [Real.dist_eq]
  have hlow : 1 ≤ max 1 ‖a coord‖ := le_max_left _ _
  have hupp : max 1 ‖a coord‖ < 1 + ε :=
    max_lt (lt_add_of_pos_right 1 hε) hcoord
  exact (abs_lt.mpr ⟨by linarith, by linarith⟩)

/-- Unit normalization changes every value of a lift by a c₀-sequence as
soon as the corona class of the lifted unit has norm at most one. -/
theorem normalizeMatrixLift_quotient_eq
    {C : Type*} [AddCommMonoid C] [Module ℂ C] [One C]
    (lift : C →ₗ[ℂ] BoundedMatrixSequence X)
    (hunit : ‖normMatrixCStarCoronaMk X (lift 1)‖ ≤ 1)
    (c : C) : normMatrixCStarCoronaMk X (normalizeMatrixLift X lift c) =
      normMatrixCStarCoronaMk X (lift c) := by
  have hmax := tendsto_max_one_coord_norm_of_corona_norm_le_one X (lift 1) hunit
  have hs : Tendsto (unitNormalizationScale X lift) atTop (nhds 1) := by
    change Tendsto (fun coord ↦ (max 1 ‖lift 1 coord‖)⁻¹) atTop (nhds 1)
    simpa only [inv_one] using hmax.inv₀ one_ne_zero
  have hsC : Tendsto (fun n ↦ (unitNormalizationScale X lift n : ℂ))
      atTop (nhds 1) := (Complex.continuous_ofReal.tendsto 1).comp hs
  have hscalar : Tendsto
      (fun n ↦ ‖(unitNormalizationScale X lift n : ℂ) - 1‖)
      atTop (nhds 0) := by
    have hsub : Tendsto
        (fun n ↦ (unitNormalizationScale X lift n : ℂ) - 1)
        atTop (nhds ((1 : ℂ) - 1)) := hsC.sub tendsto_const_nhds
    have hnorm := hsub.norm
    simpa only [sub_self, norm_zero] using hnorm
  have hnull : IsNullMatrixSequence X cofinite
      (normalizeMatrixLift X lift c - lift c) := by
    rw [IsNullMatrixSequence, Nat.cofinite_eq_atTop]
    refine squeeze_zero'
      (g := fun n ↦
        ‖(unitNormalizationScale X lift n : ℂ) - 1‖ * ‖lift c‖)
      (Eventually.of_forall fun n ↦ norm_nonneg _) ?_ ?_
    · exact Eventually.of_forall fun n ↦ by
        have hcoord : (normalizeMatrixLift X lift c - lift c) n =
            ((unitNormalizationScale X lift n : ℂ) - 1) • lift c n := by
          change (unitNormalizationScale X lift n : ℂ) • lift c n -
            lift c n = _
          rw [sub_smul, one_smul]
        rw [hcoord, norm_smul]
        exact mul_le_mul_of_nonneg_left
          (boundedMatrixSequence_coord_norm_le X (lift c) n)
          (norm_nonneg _)
    · simpa only [zero_mul, mul_comm] using hscalar.const_mul ‖lift c‖
  rw [← sub_eq_zero, ← map_sub, normMatrixCStarCoronaMk_eq_zero_iff]
  exact hnull

/-- A fixed set-theoretic section of the matrix-corona quotient map.

No algebraic property is claimed: this section is used only to lift the
finitely many entries of a factor of a positive matrix. -/
def coronaRepresentative (z : NormMatrixCStarCorona X) :
    BoundedMatrixSequence X :=
  Classical.choose (normMatrixCStarCoronaMk_surjective X z)

@[simp] theorem coronaRepresentative_mk (z : NormMatrixCStarCorona X) :
    normMatrixCStarCoronaMk X (coronaRepresentative X z) = z :=
  Classical.choose_spec (normMatrixCStarCoronaMk_surjective X z)

/-- Lift a finite matrix over the corona entry by entry.  This map is not
asserted to be linear; it is applied only to a chosen factor. -/
def entrywiseRepresentative {k : ℕ}
    (P : CStarMatrix (Fin k) (Fin k) (NormMatrixCStarCorona X)) :
    CStarMatrix (Fin k) (Fin k) (BoundedMatrixSequence X) :=
  CStarMatrix.ofMatrix (Matrix.of fun i j ↦ coronaRepresentative X (P i j))

@[simp] theorem entrywiseRepresentative_mk_apply {k : ℕ}
    (P : CStarMatrix (Fin k) (Fin k) (NormMatrixCStarCorona X))
    (i j : Fin k) :
    normMatrixCStarCoronaMk X (entrywiseRepresentative X P i j) = P i j := by
  exact coronaRepresentative_mk X (P i j)

/-- **Positive matrices over the matrix corona lift positively.**

Positivity is expressed in the repository's order-free C-star form
`C = star P * P`.  The conclusion supplies a matrix `Chat` over the bounded
product, a factorization of `Chat`, and entrywise equality after applying the
corona quotient map. -/
theorem exists_positive_cstarMatrix_lift {k : ℕ}
    (C : CStarMatrix (Fin k) (Fin k) (NormMatrixCStarCorona X))
    (hC : ∃ P : CStarMatrix (Fin k) (Fin k) (NormMatrixCStarCorona X),
      C = star P * P) :
    ∃ Chat : CStarMatrix (Fin k) (Fin k) (BoundedMatrixSequence X),
      (∃ R : CStarMatrix (Fin k) (Fin k) (BoundedMatrixSequence X),
        Chat = star R * R) ∧
      ∀ i j : Fin k,
        normMatrixCStarCoronaMk X (Chat i j) = C i j := by
  obtain ⟨P, rfl⟩ := hC
  let R := entrywiseRepresentative X P
  refine ⟨star R * R, ⟨R, rfl⟩, ?_⟩
  intro i j
  change normMatrixCStarCoronaMk X
      (∑ r : Fin k, star (R r i) * R r j) =
    ∑ r : Fin k, star (P r i) * P r j
  rw [map_sum]
  refine Finset.sum_congr rfl fun r _ ↦ ?_
  rw [map_mul, ← normMatrixCStarCorona_star_mk,
    entrywiseRepresentative_mk_apply, entrywiseRepresentative_mk_apply]

/-! ## Completely positive lifting for a full matrix domain -/

/-- The Choi matrix of a linear map out of a full matrix algebra. -/
def choiMatrix {k : ℕ} {D : Type*} [NonUnitalCStarAlgebra D]
    (f : Matrix (Fin k) (Fin k) ℂ →ₗ[ℂ] D) :
    CStarMatrix (Fin k) (Fin k) D :=
  CStarMatrix.ofMatrix
    (Matrix.of fun i j ↦ f (Matrix.single i j 1))

@[simp] theorem choiMatrix_apply {k : ℕ} {D : Type*}
    [NonUnitalCStarAlgebra D]
    (f : Matrix (Fin k) (Fin k) ℂ →ₗ[ℂ] D) (i j : Fin k) :
    choiMatrix f i j = f (Matrix.single i j 1) := rfl

/-- A row of matrix units has the standard matrix-unit Gram matrix. -/
theorem star_single_row_mul_single_row {k : ℕ} (o i j : Fin k) :
    star (Matrix.single o i (1 : ℂ)) * Matrix.single o j (1 : ℂ) =
      Matrix.single i j 1 := by
  rw [CStarExactness.star_matrix_single,
    Matrix.single_mul_single_same, star_one, one_mul]

/-- The Choi matrix of a completely positive map out of a nonzero full matrix
algebra is positive, in the factorization sense used throughout the
repository. -/
theorem exists_factor_choiMatrix_of_cp {k : ℕ} [Nonempty (Fin k)]
    {D : Type*} [NonUnitalCStarAlgebra D]
    (f : Matrix (Fin k) (Fin k) ℂ →ₗ[ℂ] D)
    (hf : CStarExactness.IsCompletelyPositive f) :
    ∃ P : CStarMatrix (Fin k) (Fin k) D, choiMatrix f = star P * P := by
  let o : Fin k := Classical.choice inferInstance
  let a : Fin k → Matrix (Fin k) (Fin k) ℂ := fun i ↦ Matrix.single o i 1
  haveI : NeZero k := ⟨Nat.ne_of_gt (Fin.pos_iff_nonempty.mpr inferInstance)⟩
  obtain ⟨N, hN⟩ := CStarExactness.star_col_mul_col a
  let E : CStarMatrix (Fin k) (Fin k) (Matrix (Fin k) (Fin k) ℂ) :=
    CStarMatrix.ofMatrix (Matrix.of fun i j ↦ Matrix.single i j 1)
  have hE : E = star N * N := by
    rw [← hN]
    show (E : Matrix (Fin k) (Fin k) (Matrix (Fin k) (Fin k) ℂ)) =
      (CStarMatrix.ofMatrix
        (Matrix.of fun i j ↦ star (a i) * a j) :
          Matrix (Fin k) (Fin k) (Matrix (Fin k) (Fin k) ℂ))
    funext i j
    exact (star_single_row_mul_single_row o i j).symm
  obtain ⟨P, hP⟩ := hf k E ⟨N, hE⟩
  refine ⟨P, ?_⟩
  rw [← hP]
  ext i j
  rfl

/-- Every matrix is the sum of its scalar matrix-unit coordinates. -/
theorem matrix_eq_sum_smul_single {k : ℕ} (T : Matrix (Fin k) (Fin k) ℂ) :
    T = ∑ i : Fin k, ∑ j : Fin k, T i j • Matrix.single i j 1 := by
  classical
  ext p q
  rw [Matrix.sum_apply, Finset.sum_eq_single p]
  · rw [Matrix.sum_apply, Finset.sum_eq_single q]
    · simp
    · intro j _ hj
      simp [hj]
    · simp
  · intro i _ hi
    simp [Matrix.sum_apply, hi]
  · simp

/-- **Finite-dimensional Choi--Effros lifting for the concrete matrix
corona.**  Every completely positive map from a nonzero full matrix algebra
to the norm-matrix corona has an exact completely positive linear lift to the
bounded matrix product.

This theorem contains no lifting premise.  Its proof is the Choi construction:
lift a Gram factor of the Choi matrix entrywise, rebuild the map from the
lifted Gram family, and use the matrix-unit expansion to verify the quotient
identity. -/
theorem exists_completelyPositive_matrix_lift {k : ℕ} [Nonempty (Fin k)]
    (f : Matrix (Fin k) (Fin k) ℂ →ₗ[ℂ] NormMatrixCStarCorona X)
    (hf : CStarExactness.IsCompletelyPositive f) :
    ∃ lift : Matrix (Fin k) (Fin k) ℂ →ₗ[ℂ] BoundedMatrixSequence X,
      CStarExactness.IsCompletelyPositive
        (A := Matrix (Fin k) (Fin k) ℂ) (B := BoundedMatrixSequence X) lift ∧
      ∀ T, normMatrixCStarCoronaQuotient X (lift T) = f T := by
  obtain ⟨P, hP⟩ := exists_factor_choiMatrix_of_cp f hf
  obtain ⟨Chat, ⟨R, hR⟩, hChat⟩ :=
    exists_positive_cstarMatrix_lift X (choiMatrix f) ⟨P, hP⟩
  let lift : Matrix (Fin k) (Fin k) ℂ →ₗ[ℂ] BoundedMatrixSequence X :=
    matrixGramChoiMap (fun s i ↦ R s i)
  refine ⟨lift, isCompletelyPositive_matrixGramChoiMap _, ?_⟩
  intro T
  have hChatEntry : ∀ i j : Fin k,
      Chat i j = ∑ s : Fin k, star (R s i) * R s j := by
    intro i j
    rw [hR, CStarExactness.cstarMatrix_mul_apply]
    exact Finset.sum_congr rfl fun s _ ↦ by
      rw [CStarExactness.cstarMatrix_star_apply]
  change normMatrixCStarCoronaQuotient X
      (matrixGramChoiMap (fun s i ↦ R s i) T) = f T
  rw [matrixGramChoiMap_apply]
  simp_rw [← hChatEntry]
  rw [map_sum]
  calc
    (∑ i : Fin k, normMatrixCStarCoronaQuotient X
        (∑ j : Fin k, T i j • Chat i j)) =
        ∑ i : Fin k, ∑ j : Fin k,
          T i j • f (Matrix.single i j 1) := by
      refine Finset.sum_congr rfl fun i _ ↦ ?_
      rw [map_sum]
      refine Finset.sum_congr rfl fun j _ ↦ ?_
      rw [map_smul]
      exact congrArg (fun z ↦ T i j • z)
        ((hChat i j).trans (choiMatrix_apply f i j))
    _ = f (∑ i : Fin k, ∑ j : Fin k,
          T i j • Matrix.single i j 1) := by
      symm
      rw [map_sum]
      refine Finset.sum_congr rfl fun i _ ↦ ?_
      rw [map_sum]
      exact Finset.sum_congr rfl fun j _ ↦ (map_smul f (T i j)
        (Matrix.single i j 1))
    _ = f T := by rw [← matrix_eq_sum_smul_single T]

/-- **Completely positive contractive lifting for the concrete matrix
corona.**  Every completely positive contraction from a nonzero full matrix
algebra to the norm-matrix corona has an exact completely positive contractive
linear lift to the bounded matrix product. -/
theorem exists_completelyPositiveContractive_matrix_lift
    {k : ℕ} [Nonempty (Fin k)]
    (f : Matrix (Fin k) (Fin k) ℂ →ₗ[ℂ] NormMatrixCStarCorona X)
    (hf : CStarExactness.IsCompletelyPositive f)
    (hcontract : ∀ T, ‖f T‖ ≤ ‖T‖) :
    ∃ lift : Matrix (Fin k) (Fin k) ℂ →ₗ[ℂ] BoundedMatrixSequence X,
      CStarExactness.IsCompletelyPositive lift ∧
      (∀ T, ‖lift T‖ ≤ ‖T‖) ∧
      ∀ T, normMatrixCStarCoronaQuotient X (lift T) = f T := by
  obtain ⟨lift, hliftCP, hlift⟩ := exists_completelyPositive_matrix_lift X f hf
  let normalized := normalizeMatrixLift X lift
  have hunit : ‖normMatrixCStarCoronaMk X (lift 1)‖ ≤ 1 := by
    have hunitEq : normMatrixCStarCoronaMk X (lift 1) = f 1 := by
      exact hlift 1
    rw [hunitEq]
    exact (hcontract 1).trans_eq norm_one
  refine ⟨normalized, isCompletelyPositive_normalizeMatrixLift X lift hliftCP,
    normalizeMatrixLift_norm_le X lift hliftCP, ?_⟩
  intro T
  change normMatrixCStarCoronaMk X (normalizeMatrixLift X lift T) = f T
  rw [normalizeMatrixLift_quotient_eq X lift hunit]
  exact hlift T

end

end BlackadarKirchberg
end GroupApproximation

open GroupApproximation.BlackadarKirchberg

#audit_axioms exists_positive_cstarMatrix_lift
#audit_axioms exists_completelyPositive_matrix_lift
#audit_axioms exists_completelyPositiveContractive_matrix_lift
