import GroupApproximation.Kazhdan.KazhdanGNS
import GroupApproximation.Sofic.KazhdanCornerMatrices
import GroupApproximation.Sofic.FiniteStageRobustGap

/-!
# Vector-state compactness for weak-MF microstates

This file transfers arbitrary unit-vector matrix coefficients of a weak-MF
approximation to an exact real orthogonal representation.  It is the
compactness engine used to rule out spurious finite-stage spectrum between
the moving Kazhdan spectrum and the invariant eigenvalue `1`.

## The ultrafilter locus

`non_mf_groups_exist.tex` used to carry a section titled "The finite-stage
transport proof", advertising a proof of the Kazhdan transport theorem
"quantitatively at each single coordinate `n` and with no ultrafilter", whose
estimate (i) carried a `\leanverified` badge pointing at
`hermitianAverage_eventually_no_intermediate_eigenvalues` below.  That proof
*does* use an ultrafilter: a `Hyperreal` standard part is a limit
along the hyperfilter on `ℕ`.

**The section, and with it the badge, are gone** -- commit `3a45fa60`
("Editorial pass: rewrite orbit collapse, cut what nothing uses") deleted the
appendix and the remark announcing it.  The discrepancy recorded below is
therefore no longer a live manuscript defect; it is kept because the
declarations it names are still here and still carry the dependency, and a
future badge on any of them would reintroduce the same false claim.  The contaminated declarations of this file are
exactly

* `correlationHyperreal`, `gramCorrelationHyperreal`, `limitingCorrelation`,
  `limitingPositiveDefiniteFunction` and every result about them;
* `combinationNormSqHyperreal` and the `stdPart_*` results;
* `HermitianEigenpairSequence.valueHyperreal`,
  `stdPart_displacement_eq_eigenvaluePolynomial`;
* `finiteAveragingDisplacementNormSq_eventually_lt` and
  `hermitianAverage_eventually_no_intermediate_eigenvalues`.

The limit is not removable by refactoring.  The statement being proved is
about an *almost* representation, whereas property `(T)` is a statement about
exact unitary representations; the passage from one to the other either takes
a limit (as here, producing a non-effective `∃ N`) or uses a sum-of-squares
certificate for `(T)` in the group algebra, which is not formalized in this
corpus.  Compare the module docstring of
`GroupApproximation/Sofic/KazhdanCornerCompression.lean`, which records the
same phenomenon for the operator-norm almost-spectral-gap theorem of Bader
(Dogon--Vigdorovich, Theorem 7.10), whose proof uses exactly that certificate.

Everything downstream of the `∃ N` *is* explicit, and lives in the
ultrafilter-free module `GroupApproximation/Sofic/FiniteStageRobustGap.lean`.
`hermitianAverage_eventually_eigenvector_displacement_le` at the end of this
file is the composition: one non-effective `N`, and after it a printed
constant.
-/

namespace GroupApproximation
namespace WeakMFVectorGNS

open Filter Matrix
open KazhdanFiniteModel
open KazhdanCornerMatrices
open scoped InnerProduct Matrix.Norms.L2Operator

variable {G : Type} [Group G]

/-- A unit vector in every matrix model of a weak-MF approximation. -/
structure UnitVectorSequence (A : OpAlmostRepresentation G) where
  vec : ∀ n, EuclideanSpace ℂ (A.model n)
  norm_eq_one : ∀ n, ‖vec n‖ = 1

/-- Every weak-MF approximation has a canonical sequence of coordinate unit
vectors.  The positive model cardinality stored in the approximation supplies
the coordinate at each stage. -/
noncomputable def UnitVectorSequence.coordinate
    (A : OpAlmostRepresentation G) : UnitVectorSequence A where
  vec n := EuclideanSpace.single
    (Classical.choice (Fintype.card_pos_iff.mp (A.modelNonempty n))) 1
  norm_eq_one n := by
    rw [PiLp.norm_single]
    norm_num

/-- The unitary assigned to a group element, acting on its Euclidean model. -/
noncomputable def translate (A : OpAlmostRepresentation G) (n : ℕ) (g : G)
    (x : EuclideanSpace ℂ (A.model n)) : EuclideanSpace ℂ (A.model n) :=
  (Matrix.toEuclideanCLM (n := A.model n) (𝕜 := ℂ))
    (A.map n g : Matrix (A.model n) (A.model n) ℂ) x

/-- A finite-stage unitary microstate acts isometrically. -/
theorem norm_translate (A : OpAlmostRepresentation G) (n : ℕ) (g : G)
    (x : EuclideanSpace ℂ (A.model n)) :
    ‖translate A n g x‖ = ‖x‖ := by
  let u : unitary
      (EuclideanSpace ℂ (A.model n) →L[ℂ] EuclideanSpace ℂ (A.model n)) :=
    ⟨(Matrix.toEuclideanCLM (n := A.model n) (𝕜 := ℂ))
        (A.map n g : Matrix (A.model n) (A.model n) ℂ),
      Unitary.map_mem (Matrix.toEuclideanCLM (n := A.model n) (𝕜 := ℂ))
        (A.map n g).2⟩
  exact Unitary.norm_map u x

/-- Real part of the matrix coefficient of the distinguished unit vector. -/
noncomputable def correlation (A : OpAlmostRepresentation G)
    (v : UnitVectorSequence A) (n : ℕ) (g : G) : ℝ :=
  inner ℝ (v.vec n) (translate A n g (v.vec n))

/-- Real Gram coefficient of two translates of the distinguished vector. -/
noncomputable def gramCorrelation (A : OpAlmostRepresentation G)
    (v : UnitVectorSequence A) (n : ℕ) (g h : G) : ℝ :=
  inner ℝ (translate A n g (v.vec n))
    (translate A n h (v.vec n))

theorem gramCorrelation_comm (A : OpAlmostRepresentation G)
    (v : UnitVectorSequence A) (n : ℕ) (g h : G) :
    gramCorrelation A v n g h = gramCorrelation A v n h g := by
  unfold gramCorrelation
  exact real_inner_comm _ _

/-- Every coefficient is in the real unit interval. -/
theorem abs_correlation_le_one (A : OpAlmostRepresentation G)
    (v : UnitVectorSequence A) (n : ℕ) (g : G) :
    |correlation A v n g| ≤ 1 := by
  unfold correlation
  calc
    |inner ℝ (v.vec n) (translate A n g (v.vec n))| ≤
        ‖v.vec n‖ * ‖translate A n g (v.vec n)‖ :=
      abs_real_inner_le_norm _ _
    _ = 1 := by rw [norm_translate, v.norm_eq_one]; norm_num

/-- Every Gram coefficient is in the real unit interval. -/
theorem abs_gramCorrelation_le_one (A : OpAlmostRepresentation G)
    (v : UnitVectorSequence A) (n : ℕ) (g h : G) :
    |gramCorrelation A v n g h| ≤ 1 := by
  unfold gramCorrelation
  calc
    |inner ℝ (translate A n g (v.vec n))
        (translate A n h (v.vec n))| ≤
        ‖translate A n g (v.vec n)‖ *
          ‖translate A n h (v.vec n)‖ := abs_real_inner_le_norm _ _
    _ = 1 := by rw [norm_translate, norm_translate, v.norm_eq_one]; norm_num

/-- Finite real Gram quadratic forms are nonnegative. -/
theorem gramCorrelation_quadratic_nonneg (A : OpAlmostRepresentation G)
    (v : UnitVectorSequence A) (F : Finset G) (c : G → ℝ) (n : ℕ) :
    0 ≤ ∑ i ∈ F, ∑ j ∈ F,
      c i * c j * gramCorrelation A v n i j := by
  classical
  let z : EuclideanSpace ℂ (A.model n) :=
    ∑ i ∈ F, c i • translate A n i (v.vec n)
  have hz : 0 ≤ ‖z‖ ^ 2 := sq_nonneg _
  rw [← real_inner_self_eq_norm_sq] at hz
  convert hz using 1
  simp_rw [z, sum_inner, inner_sum, real_inner_smul_left,
    real_inner_smul_right]
  simp only [gramCorrelation]
  refine Finset.sum_congr rfl fun i _ ↦ Finset.sum_congr rfl fun j _ ↦ ?_
  ring

/-- On complex Euclidean space, the coordinatewise real inner product is
the real part of the complex inner product. -/
theorem real_inner_eq_re_inner {Y : Type*} [Fintype Y]
    (x y : EuclideanSpace ℂ Y) :
    inner ℝ x y = (inner ℂ x y).re := by
  simp [PiLp.inner_apply, Complex.inner]

/-- The exact relative operator built from two assigned unitaries. -/
noncomputable def relativeTranslate (A : OpAlmostRepresentation G)
    (n : ℕ) (g h : G) (x : EuclideanSpace ℂ (A.model n)) :
    EuclideanSpace ℂ (A.model n) :=
  (Matrix.toEuclideanCLM (n := A.model n) (𝕜 := ℂ))
    ((A.map n g : Matrix (A.model n) (A.model n) ℂ)ᴴ * A.map n h) x

/-- A Gram coefficient is the coefficient of the exact relative operator
`U_g⁺ U_h`. -/
theorem gramCorrelation_eq_relativeTranslate (A : OpAlmostRepresentation G)
    (v : UnitVectorSequence A) (n : ℕ) (g h : G) :
    gramCorrelation A v n g h =
      inner ℝ (v.vec n) (relativeTranslate A n g h (v.vec n)) := by
  rw [gramCorrelation, real_inner_eq_re_inner, real_inner_eq_re_inner]
  apply congrArg Complex.re
  let T := Matrix.toEuclideanCLM (n := A.model n) (𝕜 := ℂ)
  let Ug : EuclideanSpace ℂ (A.model n) →L[ℂ]
      EuclideanSpace ℂ (A.model n) :=
    T (A.map n g : Matrix (A.model n) (A.model n) ℂ)
  let Uh : EuclideanSpace ℂ (A.model n) →L[ℂ]
      EuclideanSpace ℂ (A.model n) :=
    T (A.map n h : Matrix (A.model n) (A.model n) ℂ)
  have hadj : Ug† = T
      ((A.map n g : Matrix (A.model n) (A.model n) ℂ)ᴴ) := by
    calc
      Ug† = star Ug := (ContinuousLinearMap.star_eq_adjoint Ug).symm
      _ = T (star (A.map n g : Matrix (A.model n) (A.model n) ℂ)) :=
        (map_star T (A.map n g : Matrix (A.model n) (A.model n) ℂ)).symm
      _ = T ((A.map n g : Matrix (A.model n) (A.model n) ℂ)ᴴ) := by
        rw [Matrix.star_eq_conjTranspose]
  calc
    inner ℂ (translate A n g (v.vec n)) (translate A n h (v.vec n)) =
        inner ℂ (Ug (v.vec n)) (Uh (v.vec n)) := rfl
    _ = inner ℂ (v.vec n) ((Ug†) (Uh (v.vec n))) :=
      (ContinuousLinearMap.adjoint_inner_right Ug (v.vec n)
        (Uh (v.vec n))).symm
    _ = inner ℂ (v.vec n) (relativeTranslate A n g h (v.vec n)) := by
      rw [hadj]
      change inner ℂ (v.vec n)
          ((T ((A.map n g : Matrix (A.model n) (A.model n) ℂ)ᴴ))
            ((T (A.map n h : Matrix (A.model n) (A.model n) ℂ)) (v.vec n))) =
        inner ℂ (v.vec n)
          ((T ((A.map n g : Matrix (A.model n) (A.model n) ℂ)ᴴ * A.map n h))
            (v.vec n))
      rw [map_mul]
      rfl

/-- A unit-vector matrix coefficient is bounded by the matrix operator norm. -/
theorem abs_real_inner_matrix_apply_le {Y : Type*} [Fintype Y]
    [DecidableEq Y] (C : Matrix Y Y ℂ) (x : EuclideanSpace ℂ Y)
    (hx : ‖x‖ = 1) :
    |inner ℝ x ((Matrix.toEuclideanCLM (n := Y) (𝕜 := ℂ)) C x)| ≤ ‖C‖ := by
  calc
    |inner ℝ x ((Matrix.toEuclideanCLM (n := Y) (𝕜 := ℂ)) C x)| ≤
        ‖x‖ * ‖(Matrix.toEuclideanCLM (n := Y) (𝕜 := ℂ)) C x‖ :=
      abs_real_inner_le_norm _ _
    _ = ‖(Matrix.toEuclideanCLM (n := Y) (𝕜 := ℂ)) C x‖ := by rw [hx, one_mul]
    _ ≤ ‖(Matrix.toEuclideanCLM (n := Y) (𝕜 := ℂ)) C‖ * ‖x‖ :=
      ContinuousLinearMap.le_opNorm _ _
    _ = ‖C‖ := by rw [Matrix.l2_opNorm_toEuclideanCLM, hx, mul_one]

/-- The coefficient assigned to `g⁻¹h` differs from the actual Gram
coefficient by at most the corresponding operator-norm multiplicative
defect. -/
theorem abs_correlation_sub_gram_le (A : OpAlmostRepresentation G)
    (v : UnitVectorSequence A) (n : ℕ) (g h : G) :
    |correlation A v n (g⁻¹ * h) - gramCorrelation A v n g h| ≤
      ‖(A.map n (g⁻¹ * h) : Matrix (A.model n) (A.model n) ℂ) -
        (A.map n g : Matrix (A.model n) (A.model n) ℂ)ᴴ * A.map n h‖ := by
  rw [correlation, gramCorrelation_eq_relativeTranslate]
  rw [← inner_sub_right]
  let C : Matrix (A.model n) (A.model n) ℂ :=
    (A.map n (g⁻¹ * h) : Matrix (A.model n) (A.model n) ℂ) -
      (A.map n g : Matrix (A.model n) (A.model n) ℂ)ᴴ * A.map n h
  have happly : translate A n (g⁻¹ * h) (v.vec n) -
      relativeTranslate A n g h (v.vec n) =
        (Matrix.toEuclideanCLM (n := A.model n) (𝕜 := ℂ)) C (v.vec n) := by
    unfold translate relativeTranslate C
    rw [map_sub]
    rfl
  rw [happly]
  change |inner ℝ (v.vec n)
      ((Matrix.toEuclideanCLM (n := A.model n) (𝕜 := ℂ)) C (v.vec n))| ≤ ‖C‖
  exact abs_real_inner_matrix_apply_le C (v.vec n) (v.norm_eq_one n)

/-- Relative weak-MF coefficients converge to the corresponding Gram
coefficients. -/
theorem correlation_sub_gram_tendsto_zero (A : OpAlmostRepresentation G)
    (v : UnitVectorSequence A) (g h : G) :
    Tendsto (fun n ↦ correlation A v n (g⁻¹ * h) -
      gramCorrelation A v n g h) atTop (nhds 0) := by
  refine Metric.tendsto_atTop.mpr fun ε hε ↦ ?_
  obtain ⟨N, hN⟩ := map_inv_mul_vanishing A g h (ε / 2) (by linarith)
  refine ⟨N, fun n hn ↦ ?_⟩
  rw [dist_zero_right, Real.norm_eq_abs]
  exact (abs_correlation_sub_gram_le A v n g h).trans_lt
    ((hN n hn).trans_lt (by linarith))

/-! ## The limiting positive-definite function -/

noncomputable def correlationHyperreal (A : OpAlmostRepresentation G)
    (v : UnitVectorSequence A) (g : G) : Hyperreal :=
  Hyperreal.ofSeq fun n ↦ correlation A v n g

noncomputable def gramCorrelationHyperreal (A : OpAlmostRepresentation G)
    (v : UnitVectorSequence A) (g h : G) : Hyperreal :=
  Hyperreal.ofSeq fun n ↦ gramCorrelation A v n g h

theorem correlationHyperreal_finite (A : OpAlmostRepresentation G)
    (v : UnitVectorSequence A) (g : G) :
    0 ≤ ArchimedeanClass.mk (correlationHyperreal A v g) := by
  apply ArchimedeanClass.mk_nonneg_of_le_of_le_of_archimedean
    Hyperreal.coeRingHom (r := (-1 : ℝ)) (s := (1 : ℝ))
  · change Hyperreal.ofSeq (fun _ : ℕ ↦ (-1 : ℝ)) ≤
      Hyperreal.ofSeq (fun n ↦ correlation A v n g)
    rw [Hyperreal.ofSeq_le_ofSeq]
    exact Filter.Eventually.of_forall fun n ↦
      (abs_le.mp (abs_correlation_le_one A v n g)).1
  · change Hyperreal.ofSeq (fun n ↦ correlation A v n g) ≤
      Hyperreal.ofSeq (fun _ : ℕ ↦ (1 : ℝ))
    rw [Hyperreal.ofSeq_le_ofSeq]
    exact Filter.Eventually.of_forall fun n ↦
      (abs_le.mp (abs_correlation_le_one A v n g)).2

theorem gramCorrelationHyperreal_finite (A : OpAlmostRepresentation G)
    (v : UnitVectorSequence A) (g h : G) :
    0 ≤ ArchimedeanClass.mk (gramCorrelationHyperreal A v g h) := by
  apply ArchimedeanClass.mk_nonneg_of_le_of_le_of_archimedean
    Hyperreal.coeRingHom (r := (-1 : ℝ)) (s := (1 : ℝ))
  · change Hyperreal.ofSeq (fun _ : ℕ ↦ (-1 : ℝ)) ≤
      Hyperreal.ofSeq (fun n ↦ gramCorrelation A v n g h)
    rw [Hyperreal.ofSeq_le_ofSeq]
    exact Filter.Eventually.of_forall fun n ↦
      (abs_le.mp (abs_gramCorrelation_le_one A v n g h)).1
  · change Hyperreal.ofSeq (fun n ↦ gramCorrelation A v n g h) ≤
      Hyperreal.ofSeq (fun _ : ℕ ↦ (1 : ℝ))
    rw [Hyperreal.ofSeq_le_ofSeq]
    exact Filter.Eventually.of_forall fun n ↦
      (abs_le.mp (abs_gramCorrelation_le_one A v n g h)).2

theorem gramCorrelationHyperreal_comm (A : OpAlmostRepresentation G)
    (v : UnitVectorSequence A) (g h : G) :
    gramCorrelationHyperreal A v g h = gramCorrelationHyperreal A v h g := by
  apply congrArg Hyperreal.ofSeq
  funext n
  exact gramCorrelation_comm A v n g h

theorem correlationHyperreal_sub_gram_mk_pos
    (A : OpAlmostRepresentation G) (v : UnitVectorSequence A) (g h : G) :
    0 < ArchimedeanClass.mk
      (correlationHyperreal A v (g⁻¹ * h) -
        gramCorrelationHyperreal A v g h) := by
  change 0 < ArchimedeanClass.mk (Hyperreal.ofSeq (fun n ↦
    correlation A v n (g⁻¹ * h) - gramCorrelation A v n g h))
  apply Hyperreal.archimedeanClassMk_pos_of_tendsto
  rw [Hyperreal.tendsto_ofSeq]
  exact (correlation_sub_gram_tendsto_zero A v g h).mono_left
    Nat.hyperfilter_le_atTop

noncomputable def limitingCorrelation (A : OpAlmostRepresentation G)
    (v : UnitVectorSequence A) (g : G) : ℝ :=
  ArchimedeanClass.stdPart (correlationHyperreal A v g)

theorem limitingCorrelation_inv_mul_eq_stdPart_gram
    (A : OpAlmostRepresentation G) (v : UnitVectorSequence A) (g h : G) :
    limitingCorrelation A v (g⁻¹ * h) =
      ArchimedeanClass.stdPart (gramCorrelationHyperreal A v g h) := by
  have hc := correlationHyperreal_finite A v (g⁻¹ * h)
  have hg := gramCorrelationHyperreal_finite A v g h
  have hsmall := correlationHyperreal_sub_gram_mk_pos A v g h
  have hzero : ArchimedeanClass.stdPart
      (correlationHyperreal A v (g⁻¹ * h) -
        gramCorrelationHyperreal A v g h) = 0 :=
    ArchimedeanClass.stdPart_eq_zero.mpr hsmall.ne'
  have hsub := ArchimedeanClass.stdPart_sub hc hg
  rw [hzero] at hsub
  unfold limitingCorrelation
  exact sub_eq_zero.mp hsub.symm

theorem limitingCorrelation_inv_mul_comm
    (A : OpAlmostRepresentation G) (v : UnitVectorSequence A) (g h : G) :
    limitingCorrelation A v (g⁻¹ * h) =
      limitingCorrelation A v (h⁻¹ * g) := by
  rw [limitingCorrelation_inv_mul_eq_stdPart_gram A v g h,
    limitingCorrelation_inv_mul_eq_stdPart_gram A v h g,
    gramCorrelationHyperreal_comm A v g h]

theorem limitingCorrelation_isPositiveDefinite
    (A : OpAlmostRepresentation G) (v : UnitVectorSequence A) :
    IsPositiveDefinite (limitingCorrelation A v) := by
  refine ⟨limitingCorrelation_inv_mul_comm A v, ?_⟩
  intro F c
  classical
  let term : G → G → Hyperreal := fun i j ↦
    ((c i * c j : ℝ) : Hyperreal) * gramCorrelationHyperreal A v i j
  let q : Hyperreal := ∑ i ∈ F, ∑ j ∈ F, term i j
  have hterm (i j : G) : 0 ≤ ArchimedeanClass.mk (term i j) :=
    hyperreal_mul_finite (hyperreal_coe_finite (c i * c j))
      (gramCorrelationHyperreal_finite A v i j)
  have hinner (i : G) :
      0 ≤ ArchimedeanClass.mk (∑ j ∈ F, term i j) :=
    hyperreal_finset_sum_finite F (term i) (fun j _ ↦ hterm i j)
  have hqfinite : 0 ≤ ArchimedeanClass.mk q :=
    hyperreal_finset_sum_finite F (fun i ↦ ∑ j ∈ F, term i j)
      (fun i _ ↦ hinner i)
  have hq : q = Hyperreal.ofSeq (fun n ↦ ∑ i ∈ F, ∑ j ∈ F,
      c i * c j * gramCorrelation A v n i j) := by
    change (∑ i ∈ F, ∑ j ∈ F,
        ofSeqRingHom (fun _ ↦ c i * c j) *
          ofSeqRingHom (fun n ↦ gramCorrelation A v n i j)) =
      ofSeqRingHom (fun n ↦ ∑ i ∈ F, ∑ j ∈ F,
        c i * c j * gramCorrelation A v n i j)
    rw [show (fun n ↦ ∑ i ∈ F, ∑ j ∈ F,
        c i * c j * gramCorrelation A v n i j) =
      ∑ i ∈ F, ∑ j ∈ F,
        fun n ↦ c i * c j * gramCorrelation A v n i j by
          funext n
          simp]
    rw [map_sum]
    apply Finset.sum_congr rfl
    intro i hi
    rw [map_sum]
    apply Finset.sum_congr rfl
    intro j hj
    rw [← map_mul]
    congr 1
  have hqnonneg : 0 ≤ q := by
    rw [hq]
    change Hyperreal.ofSeq (fun _ : ℕ ↦ (0 : ℝ)) ≤
      Hyperreal.ofSeq (fun n ↦ ∑ i ∈ F, ∑ j ∈ F,
        c i * c j * gramCorrelation A v n i j)
    rw [Hyperreal.ofSeq_le_ofSeq]
    exact Filter.Eventually.of_forall fun n ↦
      gramCorrelation_quadratic_nonneg A v F c n
  have hstdnonneg : 0 ≤ ArchimedeanClass.stdPart q :=
    ArchimedeanClass.le_stdPart_of_le Hyperreal.coeRingHom hqfinite hqnonneg
  have hstd : ArchimedeanClass.stdPart q =
      ∑ i ∈ F, ∑ j ∈ F,
        c i * c j * limitingCorrelation A v (i⁻¹ * j) := by
    calc
      ArchimedeanClass.stdPart q =
          ∑ i ∈ F, ArchimedeanClass.stdPart (∑ j ∈ F, term i j) :=
        stdPart_finset_sum F (fun i ↦ ∑ j ∈ F, term i j)
          (fun i _ ↦ hinner i)
      _ = ∑ i ∈ F, ∑ j ∈ F,
          ArchimedeanClass.stdPart (term i j) := by
        apply Finset.sum_congr rfl
        intro i hi
        exact stdPart_finset_sum F (term i) (fun j _ ↦ hterm i j)
      _ = ∑ i ∈ F, ∑ j ∈ F,
          c i * c j * limitingCorrelation A v (i⁻¹ * j) := by
        apply Finset.sum_congr rfl
        intro i hi
        apply Finset.sum_congr rfl
        intro j hj
        rw [ArchimedeanClass.stdPart_mul
          (hyperreal_coe_finite (c i * c j))
          (gramCorrelationHyperreal_finite A v i j),
          Hyperreal.stdPart_coe,
          ← limitingCorrelation_inv_mul_eq_stdPart_gram A v i j]
  rw [← hstd]
  exact hstdnonneg

/-- The exact real positive-definite function obtained from the weak-MF
vector state. -/
noncomputable def limitingPositiveDefiniteFunction
    (A : OpAlmostRepresentation G) (v : UnitVectorSequence A) :
    KazhdanGNS.PositiveDefiniteFunction G where
  toFun := limitingCorrelation A v
  isPositiveDefinite := limitingCorrelation_isPositiveDefinite A v

/-! ## Transfer of finite cyclic combinations -/

/-- Squared norm of a finite linear combination of translated vectors. -/
noncomputable def finiteCombinationNormSq {I : Type*}
    (A : OpAlmostRepresentation G) (n : ℕ)
    (x : EuclideanSpace ℂ (A.model n)) (F : Finset I)
    (w : I → G) (a : I → ℝ) : ℝ :=
  ‖∑ i ∈ F, a i • translate A n (w i) x‖ ^ 2

theorem finiteCombinationNormSq_eq_gram {I : Type*}
    (A : OpAlmostRepresentation G) (v : UnitVectorSequence A)
    (n : ℕ) (F : Finset I) (w : I → G) (a : I → ℝ) :
    finiteCombinationNormSq A n (v.vec n) F w a =
      ∑ i ∈ F, ∑ j ∈ F,
        a i * a j * gramCorrelation A v n (w i) (w j) := by
  classical
  unfold finiteCombinationNormSq gramCorrelation
  rw [← real_inner_self_eq_norm_sq]
  simp_rw [sum_inner, inner_sum, real_inner_smul_left,
    real_inner_smul_right]
  refine Finset.sum_congr rfl fun i _ ↦ Finset.sum_congr rfl fun j _ ↦ ?_
  ring

/-- Hyperreal squared norm of a fixed finite cyclic combination. -/
noncomputable def combinationNormSqHyperreal {I : Type*}
    (A : OpAlmostRepresentation G) (v : UnitVectorSequence A)
    (F : Finset I) (w : I → G) (a : I → ℝ) : Hyperreal :=
  ∑ i ∈ F, ∑ j ∈ F,
    ((a i * a j : ℝ) : Hyperreal) *
      gramCorrelationHyperreal A v (w i) (w j)

theorem combinationNormSqHyperreal_eq_ofSeq {I : Type*}
    (A : OpAlmostRepresentation G) (v : UnitVectorSequence A)
    (F : Finset I) (w : I → G) (a : I → ℝ) :
    combinationNormSqHyperreal A v F w a = Hyperreal.ofSeq (fun n ↦
      finiteCombinationNormSq A n (v.vec n) F w a) := by
  classical
  change (∑ i ∈ F, ∑ j ∈ F,
      ofSeqRingHom (fun _ ↦ a i * a j) *
        ofSeqRingHom (fun n ↦ gramCorrelation A v n (w i) (w j))) =
    ofSeqRingHom (fun n ↦ finiteCombinationNormSq A n (v.vec n) F w a)
  rw [show (fun n ↦ finiteCombinationNormSq A n (v.vec n) F w a) =
    ∑ i ∈ F, ∑ j ∈ F, fun n ↦
      a i * a j * gramCorrelation A v n (w i) (w j) by
      funext n
      rw [finiteCombinationNormSq_eq_gram]
      simp]
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro i hi
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro j hj
  rw [← map_mul]
  congr 1

theorem combinationNormSqHyperreal_finite {I : Type*}
    (A : OpAlmostRepresentation G) (v : UnitVectorSequence A)
    (F : Finset I) (w : I → G) (a : I → ℝ) :
    0 ≤ ArchimedeanClass.mk (combinationNormSqHyperreal A v F w a) := by
  apply hyperreal_finset_sum_finite F
  intro i hi
  apply hyperreal_finset_sum_finite F
  intro j hj
  exact hyperreal_mul_finite (hyperreal_coe_finite (a i * a j))
    (gramCorrelationHyperreal_finite A v (w i) (w j))

theorem stdPart_combinationNormSqHyperreal {I : Type*}
    (A : OpAlmostRepresentation G) (v : UnitVectorSequence A)
    (F : Finset I) (w : I → G) (a : I → ℝ) :
    ArchimedeanClass.stdPart (combinationNormSqHyperreal A v F w a) =
      ‖KazhdanGNS.indexedCombination
        (limitingPositiveDefiniteFunction A v) F w a‖ ^ 2 := by
  classical
  let term : I → I → Hyperreal := fun i j ↦
    ((a i * a j : ℝ) : Hyperreal) *
      gramCorrelationHyperreal A v (w i) (w j)
  have hterm (i j : I) : 0 ≤ ArchimedeanClass.mk (term i j) :=
    hyperreal_mul_finite (hyperreal_coe_finite (a i * a j))
      (gramCorrelationHyperreal_finite A v (w i) (w j))
  have hinner (i : I) :
      0 ≤ ArchimedeanClass.mk (∑ j ∈ F, term i j) :=
    hyperreal_finset_sum_finite F (term i) fun j _ ↦ hterm i j
  rw [KazhdanGNS.norm_indexedCombination_sq]
  change ArchimedeanClass.stdPart
      (∑ i ∈ F, ∑ j ∈ F, term i j) = _
  calc
    ArchimedeanClass.stdPart (∑ i ∈ F, ∑ j ∈ F, term i j) =
        ∑ i ∈ F, ArchimedeanClass.stdPart (∑ j ∈ F, term i j) :=
      stdPart_finset_sum F (fun i ↦ ∑ j ∈ F, term i j)
        (fun i _ ↦ hinner i)
    _ = ∑ i ∈ F, ∑ j ∈ F,
        ArchimedeanClass.stdPart (term i j) := by
      apply Finset.sum_congr rfl
      intro i hi
      exact stdPart_finset_sum F (term i) fun j _ ↦ hterm i j
    _ = ∑ i ∈ F, ∑ j ∈ F,
        a i * a j * limitingCorrelation A v ((w i)⁻¹ * w j) := by
      apply Finset.sum_congr rfl
      intro i hi
      apply Finset.sum_congr rfl
      intro j hj
      rw [ArchimedeanClass.stdPart_mul
        (hyperreal_coe_finite (a i * a j))
        (gramCorrelationHyperreal_finite A v (w i) (w j)),
        Hyperreal.stdPart_coe,
        ← limitingCorrelation_inv_mul_eq_stdPart_gram A v (w i) (w j)]

/-- Exact-word finite-stage version of the difference
`Avg^(k+1)x - Avg^k x`. -/
noncomputable def finiteAveragingDisplacementNormSq
    (A : OpAlmostRepresentation G) (n : ℕ)
    (x : EuclideanSpace ℂ (A.model n)) (S : Finset G) (k : ℕ) : ℝ :=
  let d := KazhdanGNS.averagingDisplacementCoefficients S k
  finiteCombinationNormSq A n x d.support id d

theorem combinationNormSqHyperreal_displacement_eq_ofSeq
    (A : OpAlmostRepresentation G) (v : UnitVectorSequence A)
    (S : Finset G) (k : ℕ) :
    let d := KazhdanGNS.averagingDisplacementCoefficients S k
    combinationNormSqHyperreal A v d.support id d =
      Hyperreal.ofSeq (fun n ↦
        finiteAveragingDisplacementNormSq A n (v.vec n) S k) := by
  exact combinationNormSqHyperreal_eq_ofSeq A v
    (KazhdanGNS.averagingDisplacementCoefficients S k).support id
    (KazhdanGNS.averagingDisplacementCoefficients S k)

theorem stdPart_averagingDisplacementNormSq
    (A : OpAlmostRepresentation G) (v : UnitVectorSequence A)
    (S : Finset G) (k : ℕ) :
    let d := KazhdanGNS.averagingDisplacementCoefficients S k
    ArchimedeanClass.stdPart
        (combinationNormSqHyperreal A v d.support id d) =
      ‖((IsKazhdanPair.orbitAverage S
          (KazhdanGNS.representation
            (limitingPositiveDefiniteFunction A v)))^[k + 1])
          (KazhdanGNS.kernelVector (limitingPositiveDefiniteFunction A v) 1) -
        ((IsKazhdanPair.orbitAverage S
          (KazhdanGNS.representation
            (limitingPositiveDefiniteFunction A v)))^[k])
          (KazhdanGNS.kernelVector
            (limitingPositiveDefiniteFunction A v) 1)‖ ^ 2 := by
  let p := limitingPositiveDefiniteFunction A v
  let d := KazhdanGNS.averagingDisplacementCoefficients S k
  dsimp only
  rw [stdPart_combinationNormSqHyperreal]
  rw [← KazhdanGNS.finsuppCombination_eq_indexed]
  have h := KazhdanGNS.iterate_orbitAverage_succ_sub_eq_finsuppCombination
    p S k
  dsimp only at h ⊢
  rw [h]

theorem stdPart_averagingDisplacementNormSq_le
    {Q : Finset G} {ε : ℝ} (hQ : IsKazhdanPair.{0, 0} G Q ε)
    (S : Finset G) (hQS : Q ⊆ S) (hone : 1 ∈ S) (hεone : ε ≤ 1)
    (A : OpAlmostRepresentation G) (v : UnitVectorSequence A) (k : ℕ) :
    let dk := KazhdanGNS.averagingDisplacementCoefficients S k
    let d0 := KazhdanGNS.averagingDisplacementCoefficients S 0
    ArchimedeanClass.stdPart
        (combinationNormSqHyperreal A v dk.support id dk) ≤
      (1 - ε ^ 2 / (4 * S.card)) ^ (2 * k) *
        ArchimedeanClass.stdPart
          (combinationNormSqHyperreal A v d0.support id d0) := by
  let p := limitingPositiveDefiniteFunction A v
  let Av := IsKazhdanPair.orbitAverage S (KazhdanGNS.representation p)
  let factor : ℝ := 1 - ε ^ 2 / (4 * S.card)
  have hnorm := KazhdanOrthogonal.norm_iterate_orbitAverage_succ_sub_le
    hQ S hQS hone hεone (KazhdanGNS.representation p)
      (KazhdanGNS.kernelVector p 1) k
  dsimp only at hnorm
  have hcardNat : 0 < S.card := Finset.card_pos.mpr ⟨1, hone⟩
  have hcard : (0 : ℝ) < S.card := by exact_mod_cast hcardNat
  have hεsq : ε ^ 2 ≤ 1 := by
    nlinarith [sq_nonneg ε, hQ.1, hεone]
  have hden : (0 : ℝ) < 4 * S.card := mul_pos (by norm_num) hcard
  have hdenOne : (1 : ℝ) ≤ 4 * S.card := by
    have : (1 : ℝ) ≤ S.card := by exact_mod_cast hcardNat
    nlinarith
  have hfrac : ε ^ 2 / (4 * S.card) ≤ 1 := by
    rw [div_le_one hden]
    exact hεsq.trans hdenOne
  have hfactor : 0 ≤ factor := by dsimp [factor]; linarith
  have hsq :
      ‖(Av^[k + 1]) (KazhdanGNS.kernelVector p 1) -
          (Av^[k]) (KazhdanGNS.kernelVector p 1)‖ ^ 2 ≤
        factor ^ (2 * k) *
          ‖Av (KazhdanGNS.kernelVector p 1) -
            KazhdanGNS.kernelVector p 1‖ ^ 2 := by
    have hleft : 0 ≤ ‖(Av^[k + 1]) (KazhdanGNS.kernelVector p 1) -
        (Av^[k]) (KazhdanGNS.kernelVector p 1)‖ := norm_nonneg _
    have hright : 0 ≤ factor ^ k *
        ‖Av (KazhdanGNS.kernelVector p 1) -
          KazhdanGNS.kernelVector p 1‖ :=
      mul_nonneg (pow_nonneg hfactor k) (norm_nonneg _)
    have hsquare := (sq_le_sq₀ hleft hright).2 hnorm
    calc
      ‖(Av^[k + 1]) (KazhdanGNS.kernelVector p 1) -
          (Av^[k]) (KazhdanGNS.kernelVector p 1)‖ ^ 2 ≤
          (factor ^ k * ‖Av (KazhdanGNS.kernelVector p 1) -
            KazhdanGNS.kernelVector p 1‖) ^ 2 := hsquare
      _ = factor ^ (2 * k) *
          ‖Av (KazhdanGNS.kernelVector p 1) -
            KazhdanGNS.kernelVector p 1‖ ^ 2 := by ring
  dsimp only
  rw [stdPart_averagingDisplacementNormSq,
    stdPart_averagingDisplacementNormSq]
  simpa [Av, p] using hsq

/-- Uniform Kazhdan contraction for exact-word displacement vectors in all
sufficiently late weak-MF models. -/
theorem finiteAveragingDisplacementNormSq_eventually_lt
    {Q : Finset G} {ε : ℝ} (hQ : IsKazhdanPair.{0, 0} G Q ε)
    (S : Finset G) (hQS : Q ⊆ S) (hone : 1 ∈ S) (hεone : ε ≤ 1)
    (A : OpAlmostRepresentation G) (k : ℕ) (δ : ℝ) (hδ : 0 < δ) :
    ∃ N : ℕ, ∀ n ≥ N, ∀ x : EuclideanSpace ℂ (A.model n), ‖x‖ = 1 →
      finiteAveragingDisplacementNormSq A n x S k <
        (1 - ε ^ 2 / (4 * S.card)) ^ (2 * k) *
          finiteAveragingDisplacementNormSq A n x S 0 + δ := by
  classical
  by_contra h
  push Not at h
  choose φ hφ x hx hbad using h
  let B := A.reindex φ hφ
  let v : UnitVectorSequence B := ⟨fun n ↦ x n, hx⟩
  let dk := KazhdanGNS.averagingDisplacementCoefficients S k
  let d0 := KazhdanGNS.averagingDisplacementCoefficients S 0
  let factor : ℝ := (1 - ε ^ 2 / (4 * S.card)) ^ (2 * k)
  let Hk : Hyperreal := combinationNormSqHyperreal B v dk.support id dk
  let H0 : Hyperreal := combinationNormSqHyperreal B v d0.support id d0
  have hHkfinite : 0 ≤ ArchimedeanClass.mk Hk :=
    combinationNormSqHyperreal_finite B v dk.support id dk
  have hH0finite : 0 ≤ ArchimedeanClass.mk H0 :=
    combinationNormSqHyperreal_finite B v d0.support id d0
  have hfactorfinite : 0 ≤ ArchimedeanClass.mk ((factor : ℝ) : Hyperreal) :=
    hyperreal_coe_finite factor
  have hprodFinite :
      0 ≤ ArchimedeanClass.mk (((factor : ℝ) : Hyperreal) * H0) :=
    hyperreal_mul_finite hfactorfinite hH0finite
  have hdiffFinite :
      0 ≤ ArchimedeanClass.mk (Hk - ((factor : ℝ) : Hyperreal) * H0) :=
    KazhdanGNS.hyperreal_sub_finite hHkfinite hprodFinite
  have hhyper : ((δ : ℝ) : Hyperreal) ≤
      Hk - ((factor : ℝ) : Hyperreal) * H0 := by
    rw [show Hk = Hyperreal.ofSeq (fun n ↦
        finiteAveragingDisplacementNormSq B n (v.vec n) S k) by
          exact combinationNormSqHyperreal_displacement_eq_ofSeq B v S k,
      show H0 = Hyperreal.ofSeq (fun n ↦
        finiteAveragingDisplacementNormSq B n (v.vec n) S 0) by
          exact combinationNormSqHyperreal_displacement_eq_ofSeq B v S 0]
    change Hyperreal.ofSeq (fun _ : ℕ ↦ δ) ≤ Hyperreal.ofSeq (fun n ↦
      finiteAveragingDisplacementNormSq B n (v.vec n) S k -
        factor * finiteAveragingDisplacementNormSq B n (v.vec n) S 0)
    rw [Hyperreal.ofSeq_le_ofSeq]
    exact Filter.Eventually.of_forall fun n ↦ by
      have hn := hbad n
      change factor * finiteAveragingDisplacementNormSq B n (v.vec n) S 0 + δ ≤
        finiteAveragingDisplacementNormSq B n (v.vec n) S k at hn
      linarith
  have hstdLower : δ ≤ ArchimedeanClass.stdPart
      (Hk - ((factor : ℝ) : Hyperreal) * H0) :=
    ArchimedeanClass.le_stdPart_of_le Hyperreal.coeRingHom hdiffFinite hhyper
  have hstdDiff : ArchimedeanClass.stdPart
      (Hk - ((factor : ℝ) : Hyperreal) * H0) =
      ArchimedeanClass.stdPart Hk -
        factor * ArchimedeanClass.stdPart H0 := by
    rw [ArchimedeanClass.stdPart_sub hHkfinite hprodFinite,
      ArchimedeanClass.stdPart_mul hfactorfinite hH0finite,
      Hyperreal.stdPart_coe]
  have hcontract := stdPart_averagingDisplacementNormSq_le
    hQ S hQS hone hεone B v k
  change ArchimedeanClass.stdPart Hk ≤
    factor * ArchimedeanClass.stdPart H0 at hcontract
  rw [hstdDiff] at hstdLower
  linarith

/-! ## Exact-word combinations versus powers of the matrix average -/

/-- Evaluate a real finitely supported group-ring element in one weak-MF
matrix model. -/
noncomputable def matrixFinsuppCombination (A : OpAlmostRepresentation G)
    (n : ℕ) : (G →₀ ℝ) →ₗ[ℝ] Matrix (A.model n) (A.model n) ℂ :=
  Finsupp.linearCombination ℝ fun g ↦
    (A.map n g : Matrix (A.model n) (A.model n) ℂ)

theorem matrixFinsuppCombination_eq_sum (A : OpAlmostRepresentation G)
    (n : ℕ) (c : G →₀ ℝ) :
    matrixFinsuppCombination A n c = ∑ g ∈ c.support,
      c g • (A.map n g : Matrix (A.model n) (A.model n) ℂ) := by
  classical
  simp [matrixFinsuppCombination, Finsupp.linearCombination_apply, Finsupp.sum]

/-- Exact left translation of a finite matrix combination. -/
noncomputable def matrixExactTranslation (A : OpAlmostRepresentation G)
    (n : ℕ) (s : G) (c : G →₀ ℝ) :
    Matrix (A.model n) (A.model n) ℂ :=
  matrixFinsuppCombination A n (KazhdanGNS.translateCoefficients s c)

/-- Translation by multiplying the assigned matrices. -/
noncomputable def matrixComposedTranslation (A : OpAlmostRepresentation G)
    (n : ℕ) (s : G) (c : G →₀ ℝ) :
    Matrix (A.model n) (A.model n) ℂ :=
  (A.map n s : Matrix (A.model n) (A.model n) ℂ) *
    matrixFinsuppCombination A n c

theorem matrixExactTranslation_eq_linearCombination
    (A : OpAlmostRepresentation G) (n : ℕ) (s : G) (c : G →₀ ℝ) :
    matrixExactTranslation A n s c =
      Finsupp.linearCombination ℝ (fun g ↦
        (A.map n (s * g) : Matrix (A.model n) (A.model n) ℂ)) c := by
  induction c using Finsupp.induction with
  | zero => simp [matrixExactTranslation, matrixFinsuppCombination]
  | single_add g r c hg hr ih =>
      rw [show matrixExactTranslation A n s (Finsupp.single g r + c) =
          matrixExactTranslation A n s (Finsupp.single g r) +
            matrixExactTranslation A n s c by
            simp [matrixExactTranslation], ih]
      simp [matrixExactTranslation, matrixFinsuppCombination]

theorem matrixComposedTranslation_eq_linearCombination
    (A : OpAlmostRepresentation G) (n : ℕ) (s : G) (c : G →₀ ℝ) :
    matrixComposedTranslation A n s c =
      Finsupp.linearCombination ℝ (fun g ↦
        (A.map n s : Matrix (A.model n) (A.model n) ℂ) *
          (A.map n g : Matrix (A.model n) (A.model n) ℂ)) c := by
  classical
  rw [matrixComposedTranslation, matrixFinsuppCombination_eq_sum]
  simp only [Finsupp.linearCombination_apply, Finsupp.sum, Matrix.mul_sum]
  apply Finset.sum_congr rfl
  intro g hg
  ext i j
  change (∑ x, (A.map n s : Matrix (A.model n) (A.model n) ℂ) i x *
      ((c g : ℂ) * (A.map n g : Matrix (A.model n) (A.model n) ℂ) x j)) =
    (c g : ℂ) * ∑ x,
      (A.map n s : Matrix (A.model n) (A.model n) ℂ) i x *
        (A.map n g : Matrix (A.model n) (A.model n) ℂ) x j
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro x hx
  ring

theorem matrixExact_sub_composed_eq_sum
    (A : OpAlmostRepresentation G) (n : ℕ) (s : G) (c : G →₀ ℝ) :
    matrixExactTranslation A n s c - matrixComposedTranslation A n s c =
      ∑ g ∈ c.support, (c g : ℂ) •
        ((A.map n (s * g) : Matrix (A.model n) (A.model n) ℂ) -
          (A.map n s : Matrix (A.model n) (A.model n) ℂ) *
            (A.map n g : Matrix (A.model n) (A.model n) ℂ)) := by
  classical
  rw [matrixExactTranslation_eq_linearCombination,
    matrixComposedTranslation_eq_linearCombination]
  simp only [Finsupp.linearCombination_apply, Finsupp.sum]
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro g hg
  ext i j
  simp
  ring

theorem matrixExact_sub_composed_vanishing
    (A : OpAlmostRepresentation G) (s : G) (c : G →₀ ℝ) :
    OpNormVanishing A (fun n ↦
      matrixExactTranslation A n s c - matrixComposedTranslation A n s c) := by
  rw [show (fun n ↦ matrixExactTranslation A n s c -
      matrixComposedTranslation A n s c) = fun n ↦
        ∑ g ∈ c.support, (c g : ℂ) •
          ((A.map n (s * g) : Matrix (A.model n) (A.model n) ℂ) -
            (A.map n s : Matrix (A.model n) (A.model n) ℂ) *
              (A.map n g : Matrix (A.model n) (A.model n) ℂ)) by
      funext n
      exact matrixExact_sub_composed_eq_sum A n s c]
  exact OpNormVanishing.finset_sum c.support
    (fun g n ↦ (c g : ℂ) •
      ((A.map n (s * g) : Matrix (A.model n) (A.model n) ℂ) -
        (A.map n s : Matrix (A.model n) (A.model n) ℂ) *
          (A.map n g : Matrix (A.model n) (A.model n) ℂ)))
    (fun g _ ↦ (multiplicativeDefect_vanishing A s g).smul (c g))

/-- One recursive averaging step evaluated by exact group words agrees
asymptotically with left multiplication by the finite matrix average. -/
theorem averagingCoefficients_succ_vanishing
    (A : OpAlmostRepresentation G) (S : Finset G) (k : ℕ) :
    OpNormVanishing A (fun n ↦
      matrixFinsuppCombination A n
          (KazhdanGNS.averagingCoefficients S (k + 1)) -
        matrixAverage A S n *
          matrixFinsuppCombination A n
            (KazhdanGNS.averagingCoefficients S k)) := by
  classical
  let c := KazhdanGNS.averagingCoefficients S k
  have hsum : OpNormVanishing A (fun n ↦
      ∑ s ∈ S, (matrixExactTranslation A n s c -
        matrixComposedTranslation A n s c)) :=
    OpNormVanishing.finset_sum S
      (fun s n ↦ matrixExactTranslation A n s c -
        matrixComposedTranslation A n s c)
      (fun s _ ↦ matrixExact_sub_composed_vanishing A s c)
  have hrewrite (n : ℕ) :
      matrixFinsuppCombination A n
          (KazhdanGNS.averagingCoefficients S (k + 1)) -
        matrixAverage A S n * matrixFinsuppCombination A n c =
      ((S.card : ℂ)⁻¹) • ∑ s ∈ S,
        (matrixExactTranslation A n s c -
          matrixComposedTranslation A n s c) := by
    rw [KazhdanGNS.averagingCoefficients, map_smul, map_sum]
    simp only [matrixExactTranslation, c]
    have hprod : matrixAverage A S n * matrixFinsuppCombination A n c =
        ((S.card : ℂ)⁻¹) • ∑ s ∈ S,
          matrixComposedTranslation A n s c := by
      rw [matrixAverage, smul_mul_assoc, Finset.sum_mul]
      rfl
    rw [hprod]
    ext i j
    simp
    ring
  simpa only [c, hrewrite] using hsum.smul ((S.card : ℂ)⁻¹)

/-- Evaluated exact `k`-step averaging coefficients converge in operator
norm to the `k`th power of the matrix average. -/
theorem averagingCoefficients_sub_pow_vanishing
    (A : OpAlmostRepresentation G) (S : Finset G) (k : ℕ) :
    OpNormVanishing A (fun n ↦
      matrixFinsuppCombination A n
          (KazhdanGNS.averagingCoefficients S k) -
        (matrixAverage A S n) ^ k) := by
  induction k with
  | zero =>
      simpa [KazhdanGNS.averagingCoefficients, matrixFinsuppCombination] using
        map_one_vanishing A
  | succ k ih =>
      have hstep := averagingCoefficients_succ_vanishing A S k
      have hmul := ih.mul_left_of_norm_le_one (fun n ↦ matrixAverage A S n)
        (norm_matrixAverage_le_one A S)
      have hadd := hstep.add hmul
      have hrewrite (n : ℕ) :
          (matrixFinsuppCombination A n
              (KazhdanGNS.averagingCoefficients S (k + 1)) -
            matrixAverage A S n * matrixFinsuppCombination A n
              (KazhdanGNS.averagingCoefficients S k)) +
          matrixAverage A S n *
            (matrixFinsuppCombination A n
                (KazhdanGNS.averagingCoefficients S k) -
              matrixAverage A S n ^ k) =
          matrixFinsuppCombination A n
              (KazhdanGNS.averagingCoefficients S (k + 1)) -
            matrixAverage A S n ^ (k + 1) := by
        rw [pow_succ']
        noncomm_ring
      simpa only [hrewrite] using hadd

/-- The exact-word displacement combination converges to the corresponding
difference of consecutive powers of the matrix average. -/
theorem averagingDisplacement_sub_powers_vanishing
    (A : OpAlmostRepresentation G) (S : Finset G) (k : ℕ) :
    OpNormVanishing A (fun n ↦
      matrixFinsuppCombination A n
          (KazhdanGNS.averagingDisplacementCoefficients S k) -
        ((matrixAverage A S n) ^ (k + 1) -
          (matrixAverage A S n) ^ k)) := by
  have hk1 := averagingCoefficients_sub_pow_vanishing A S (k + 1)
  have hk := averagingCoefficients_sub_pow_vanishing A S k
  have hsub := hk1.sub hk
  have hrewrite (n : ℕ) :
      (matrixFinsuppCombination A n
          (KazhdanGNS.averagingCoefficients S (k + 1)) -
        matrixAverage A S n ^ (k + 1)) -
      (matrixFinsuppCombination A n
          (KazhdanGNS.averagingCoefficients S k) -
        matrixAverage A S n ^ k) =
      matrixFinsuppCombination A n
          (KazhdanGNS.averagingDisplacementCoefficients S k) -
        (matrixAverage A S n ^ (k + 1) - matrixAverage A S n ^ k) := by
    simp [KazhdanGNS.averagingDisplacementCoefficients]
    abel
  simpa only [hrewrite] using hsub

/-- The finite exact-word displacement norm is the matrix operator encoded
by the same finitely supported coefficients applied to the vector. -/
theorem finiteAveragingDisplacementNormSq_eq_matrix
    (A : OpAlmostRepresentation G) (n : ℕ)
    (x : EuclideanSpace ℂ (A.model n)) (S : Finset G) (k : ℕ) :
    finiteAveragingDisplacementNormSq A n x S k =
      ‖(Matrix.toEuclideanCLM (n := A.model n) (𝕜 := ℂ))
        (matrixFinsuppCombination A n
          (KazhdanGNS.averagingDisplacementCoefficients S k)) x‖ ^ 2 := by
  classical
  let d := KazhdanGNS.averagingDisplacementCoefficients S k
  change ‖∑ i ∈ d.support, d i • translate A n i x‖ ^ 2 =
    ‖(Matrix.toEuclideanCLM (n := A.model n) (𝕜 := ℂ))
      (matrixFinsuppCombination A n d) x‖ ^ 2
  rw [matrixFinsuppCombination_eq_sum, map_sum]
  have heval :
      (∑ g ∈ d.support,
        (Matrix.toEuclideanCLM (n := A.model n) (𝕜 := ℂ))
          (d g • (A.map n g : Matrix (A.model n) (A.model n) ℂ))) x =
      ∑ g ∈ d.support,
        (Matrix.toEuclideanCLM (n := A.model n) (𝕜 := ℂ))
          (d g • (A.map n g : Matrix (A.model n) (A.model n) ℂ)) x := by
    induction d.support using Finset.induction_on with
    | empty => simp
    | @insert g F hg ih => simp [Finset.sum_insert, hg, ih]
  rw [heval]
  congr 2
  apply Finset.sum_congr rfl
  intro g hg
  change (d g : ℂ) • translate A n g x =
    (Matrix.toEuclideanCLM (n := A.model n) (𝕜 := ℂ))
      ((d g : ℂ) • (A.map n g : Matrix (A.model n) (A.model n) ℂ)) x
  rw [map_smul]
  rfl

theorem opNormVanishing_pow_sub_pow
    (A : OpAlmostRepresentation G)
    (X Y : ∀ n, Matrix (A.model n) (A.model n) ℂ)
    (hXY : OpNormVanishing A (fun n ↦ X n - Y n))
    (hX : ∀ n, ‖X n‖ ≤ 1) (hY : ∀ n, ‖Y n‖ ≤ 1)
    (k : ℕ) :
    OpNormVanishing A (fun n ↦ X n ^ k - Y n ^ k) := by
  induction k with
  | zero => simpa using opNormVanishing_zero A
  | succ k ih =>
      have hleft := ih.mul_left_of_norm_le_one X hX
      have hpowY : ∀ n, ‖Y n ^ k‖ ≤ 1 := by
        intro n
        letI : Nonempty (A.model n) :=
          Fintype.card_pos_iff.mp (A.modelNonempty n)
        exact (norm_pow_le (Y n) k).trans
          (pow_le_one₀ (norm_nonneg _) (hY n))
      have hright := hXY.mul_right_of_norm_le_one (fun n ↦ Y n ^ k) hpowY
      have hadd := hleft.add hright
      have hrewrite (n : ℕ) :
          X n * (X n ^ k - Y n ^ k) + (X n - Y n) * Y n ^ k =
            X n ^ (k + 1) - Y n ^ (k + 1) := by
        rw [pow_succ', pow_succ']
        noncomm_ring
      simpa only [hrewrite] using hadd

/-- Exact-word displacement operators converge to the corresponding
Hermitian-average displacement operators. -/
theorem averagingDisplacement_sub_hermitianPowers_vanishing
    (A : OpAlmostRepresentation G) (S : Finset G)
    (hsymm : ∀ g ∈ S, g⁻¹ ∈ S) (k : ℕ) :
    OpNormVanishing A (fun n ↦
      matrixFinsuppCombination A n
          (KazhdanGNS.averagingDisplacementCoefficients S k) -
        ((hermitianAverage A S n) ^ (k + 1) -
          (hermitianAverage A S n) ^ k)) := by
  have hMH := matrixAverage_sub_hermitian_vanishing A S hsymm
  have hpow1 := opNormVanishing_pow_sub_pow A
    (fun n ↦ matrixAverage A S n) (fun n ↦ hermitianAverage A S n)
    hMH (norm_matrixAverage_le_one A S) (norm_hermitianAverage_le_one A S) (k + 1)
  have hpow0 := opNormVanishing_pow_sub_pow A
    (fun n ↦ matrixAverage A S n) (fun n ↦ hermitianAverage A S n)
    hMH (norm_matrixAverage_le_one A S) (norm_hermitianAverage_le_one A S) k
  have hpowers := hpow1.sub hpow0
  have hexact := averagingDisplacement_sub_powers_vanishing A S k
  have hadd := hexact.add hpowers
  have hrewrite (n : ℕ) :
      (matrixFinsuppCombination A n
          (KazhdanGNS.averagingDisplacementCoefficients S k) -
        (matrixAverage A S n ^ (k + 1) - matrixAverage A S n ^ k)) +
      ((matrixAverage A S n ^ (k + 1) - hermitianAverage A S n ^ (k + 1)) -
        (matrixAverage A S n ^ k - hermitianAverage A S n ^ k)) =
      matrixFinsuppCombination A n
          (KazhdanGNS.averagingDisplacementCoefficients S k) -
        (hermitianAverage A S n ^ (k + 1) - hermitianAverage A S n ^ k) := by
    abel
  simpa only [hrewrite] using hadd

theorem norm_matrixFinsuppCombination_le (A : OpAlmostRepresentation G)
    (n : ℕ) (c : G →₀ ℝ) :
    ‖matrixFinsuppCombination A n c‖ ≤ ∑ g ∈ c.support, |c g| := by
  classical
  letI : Nonempty (A.model n) :=
    Fintype.card_pos_iff.mp (A.modelNonempty n)
  rw [matrixFinsuppCombination_eq_sum]
  calc
    ‖∑ g ∈ c.support,
        c g • (A.map n g : Matrix (A.model n) (A.model n) ℂ)‖ ≤
        ∑ g ∈ c.support,
          ‖c g • (A.map n g : Matrix (A.model n) (A.model n) ℂ)‖ :=
      norm_sum_le _ _
    _ = ∑ g ∈ c.support, |c g| := by
      apply Finset.sum_congr rfl
      intro g hg
      rw [norm_smul, CStarRing.norm_of_mem_unitary (A.map n g).2,
        mul_one, Real.norm_eq_abs]

/-- Perturbing an operator in operator norm perturbs its squared norm on a
unit vector by the usual difference-of-squares bound. -/
theorem abs_normSq_apply_sub_le {Y : Type*} [Fintype Y] [DecidableEq Y]
    (C D : Matrix Y Y ℂ) (x : EuclideanSpace ℂ Y) (hx : ‖x‖ = 1) :
    |‖(Matrix.toEuclideanCLM (n := Y) (𝕜 := ℂ)) C x‖ ^ 2 -
      ‖(Matrix.toEuclideanCLM (n := Y) (𝕜 := ℂ)) D x‖ ^ 2| ≤
      ‖C - D‖ * (‖C‖ + ‖D‖) := by
  let u := (Matrix.toEuclideanCLM (n := Y) (𝕜 := ℂ)) C x
  let w := (Matrix.toEuclideanCLM (n := Y) (𝕜 := ℂ)) D x
  have hdiff : |‖u‖ - ‖w‖| ≤ ‖C - D‖ := by
    calc
      |‖u‖ - ‖w‖| ≤ ‖u - w‖ := abs_norm_sub_norm_le _ _
      _ = ‖(Matrix.toEuclideanCLM (n := Y) (𝕜 := ℂ)) (C - D) x‖ := by
        congr 1
        simp [u, w]
      _ ≤ ‖C - D‖ * ‖x‖ := ContinuousLinearMap.le_opNorm _ _
      _ = ‖C - D‖ := by rw [hx, mul_one]
  have hu : ‖u‖ ≤ ‖C‖ := by
    calc
      ‖u‖ ≤ ‖(Matrix.toEuclideanCLM (n := Y) (𝕜 := ℂ)) C‖ * ‖x‖ :=
        ContinuousLinearMap.le_opNorm _ _
      _ = ‖C‖ := by
        rw [hx, mul_one]
        exact Matrix.l2_opNorm_toEuclideanCLM C
  have hw : ‖w‖ ≤ ‖D‖ := by
    calc
      ‖w‖ ≤ ‖(Matrix.toEuclideanCLM (n := Y) (𝕜 := ℂ)) D‖ * ‖x‖ :=
        ContinuousLinearMap.le_opNorm _ _
      _ = ‖D‖ := by
        rw [hx, mul_one]
        exact Matrix.l2_opNorm_toEuclideanCLM D
  rw [show ‖u‖ ^ 2 - ‖w‖ ^ 2 = (‖u‖ - ‖w‖) * (‖u‖ + ‖w‖) by ring,
    abs_mul, abs_of_nonneg (add_nonneg (norm_nonneg _) (norm_nonneg _))]
  exact mul_le_mul hdiff (add_le_add hu hw)
    (add_nonneg (norm_nonneg _) (norm_nonneg _)) (norm_nonneg _)

/-! ## Spectral-gap transfer -/

/-- A chosen unit eigenvector of every Hermitian finite-stage average. -/
structure HermitianEigenpairSequence (A : OpAlmostRepresentation G)
    (S : Finset G) where
  vector : UnitVectorSequence A
  value : ℕ → ℝ
  eigen : ∀ n,
    (Matrix.toEuclideanCLM (n := A.model n) (𝕜 := ℂ))
      (hermitianAverage A S n) (vector.vec n) =
        (value n : ℂ) • vector.vec n

/-- A canonical finite-stage eigenpair sequence, obtained by taking the first
available vector in the orthonormal eigenbasis of each Hermitian average. -/
noncomputable def HermitianEigenpairSequence.coordinate
    (A : OpAlmostRepresentation G) (S : Finset G) :
    HermitianEigenpairSequence A S := by
  let hH : ∀ n, (hermitianAverage A S n).IsHermitian := fun n ↦
    hermitianAverage_conjTranspose A S n
  let i : ∀ n, A.model n := fun n ↦
    Classical.choice (Fintype.card_pos_iff.mp (A.modelNonempty n))
  exact {
    vector := {
      vec := fun n ↦ (hH n).eigenvectorBasis (i n)
      norm_eq_one := fun n ↦ (hH n).eigenvectorBasis.orthonormal.1 (i n) }
    value := fun n ↦ (hH n).eigenvalues (i n)
    eigen := by
      intro n
      apply PiLp.ext
      intro j
      exact congrFun ((hH n).mulVec_eigenvectorBasis (i n)) j
    }

theorem HermitianEigenpairSequence.abs_value_le_one
    {A : OpAlmostRepresentation G} {S : Finset G}
    (e : HermitianEigenpairSequence A S) (n : ℕ) : |e.value n| ≤ 1 := by
  have happly := ContinuousLinearMap.le_opNorm
    ((Matrix.toEuclideanCLM (n := A.model n) (𝕜 := ℂ))
      (hermitianAverage A S n)) (e.vector.vec n)
  rw [e.eigen, norm_smul, e.vector.norm_eq_one, mul_one] at happly
  rw [Matrix.l2_opNorm_toEuclideanCLM, mul_one] at happly
  simpa [Real.norm_eq_abs] using happly.trans (norm_hermitianAverage_le_one A S n)

theorem HermitianEigenpairSequence.power_apply
    {A : OpAlmostRepresentation G} {S : Finset G}
    (e : HermitianEigenpairSequence A S) (n k : ℕ) :
    (Matrix.toEuclideanCLM (n := A.model n) (𝕜 := ℂ))
      ((hermitianAverage A S n) ^ k) (e.vector.vec n) =
        ((e.value n : ℂ) ^ k) • e.vector.vec n := by
  induction k with
  | zero => simp
  | succ k ih =>
      rw [pow_succ', map_mul]
      change (Matrix.toEuclideanCLM (n := A.model n) (𝕜 := ℂ))
        (hermitianAverage A S n)
          ((Matrix.toEuclideanCLM (n := A.model n) (𝕜 := ℂ))
            ((hermitianAverage A S n) ^ k) (e.vector.vec n)) = _
      rw [ih, map_smul, e.eigen]
      apply PiLp.ext
      intro i
      simp [pow_succ', PiLp.smul_apply]
      ring

theorem HermitianEigenpairSequence.displacement_normSq
    {A : OpAlmostRepresentation G} {S : Finset G}
    (e : HermitianEigenpairSequence A S) (n k : ℕ) :
    ‖(Matrix.toEuclideanCLM (n := A.model n) (𝕜 := ℂ))
      ((hermitianAverage A S n) ^ (k + 1) -
        (hermitianAverage A S n) ^ k) (e.vector.vec n)‖ ^ 2 =
      (e.value n ^ (k + 1) - e.value n ^ k) ^ 2 := by
  rw [map_sub, _root_.sub_apply,
    e.power_apply, e.power_apply, ← sub_smul]
  rw [norm_smul, e.vector.norm_eq_one, mul_one]
  have hcoe : (e.value n : ℂ) ^ (k + 1) - (e.value n : ℂ) ^ k =
      ((e.value n ^ (k + 1) - e.value n ^ k : ℝ) : ℂ) := by
    push_cast
    rfl
  rw [hcoe, Complex.norm_real, Real.norm_eq_abs, sq_abs]

/-- Along any chosen eigenvector sequence, the exact-word displacement
norm converges to the scalar displacement polynomial of its eigenvalue. -/
theorem eigen_displacementNormSq_sub_scalar_tendsto_zero
    (A : OpAlmostRepresentation G) (S : Finset G)
    (hsymm : ∀ g ∈ S, g⁻¹ ∈ S)
    (e : HermitianEigenpairSequence A S) (k : ℕ) :
    Tendsto (fun n ↦
      finiteAveragingDisplacementNormSq A n (e.vector.vec n) S k -
        (e.value n ^ (k + 1) - e.value n ^ k) ^ 2)
      atTop (nhds 0) := by
  let d := KazhdanGNS.averagingDisplacementCoefficients S k
  let B : ℝ := ∑ g ∈ d.support, |d g|
  have hB : 0 < B + 2 := by
    have : 0 ≤ B := Finset.sum_nonneg fun g _ ↦ abs_nonneg _
    linarith
  have hv := averagingDisplacement_sub_hermitianPowers_vanishing A S hsymm k
  refine Metric.tendsto_atTop.mpr fun η hη ↦ ?_
  obtain ⟨N, hN⟩ := hv (η / (2 * (B + 2))) (by positivity)
  refine ⟨N, fun n hn ↦ ?_⟩
  let C := matrixFinsuppCombination A n d
  let D := (hermitianAverage A S n) ^ (k + 1) -
    (hermitianAverage A S n) ^ k
  have hC : ‖C‖ ≤ B := norm_matrixFinsuppCombination_le A n d
  have hD : ‖D‖ ≤ 2 := by
    letI : Nonempty (A.model n) :=
      Fintype.card_pos_iff.mp (A.modelNonempty n)
    calc
      ‖D‖ ≤ ‖hermitianAverage A S n ^ (k + 1)‖ +
          ‖hermitianAverage A S n ^ k‖ := norm_sub_le _ _
      _ ≤ 1 + 1 := add_le_add
        ((norm_pow_le _ _).trans
          (pow_le_one₀ (norm_nonneg _) (norm_hermitianAverage_le_one A S n)))
        ((norm_pow_le _ _).trans
          (pow_le_one₀ (norm_nonneg _) (norm_hermitianAverage_le_one A S n)))
      _ = 2 := by norm_num
  have hpert := abs_normSq_apply_sub_le C D (e.vector.vec n)
    (e.vector.norm_eq_one n)
  rw [← finiteAveragingDisplacementNormSq_eq_matrix A n
      (e.vector.vec n) S k,
    e.displacement_normSq] at hpert
  rw [dist_zero_right, Real.norm_eq_abs]
  calc
    |finiteAveragingDisplacementNormSq A n (e.vector.vec n) S k -
        (e.value n ^ (k + 1) - e.value n ^ k) ^ 2| ≤
        ‖C - D‖ * (‖C‖ + ‖D‖) := hpert
    _ ≤ (η / (2 * (B + 2))) * (B + 2) := by
      exact mul_le_mul (hN n hn) (add_le_add hC hD)
        (add_nonneg (norm_nonneg _) (norm_nonneg _)) (by positivity)
    _ < η := by
      rw [show η / (2 * (B + 2)) * (B + 2) = η / 2 by field_simp]
      linarith

noncomputable def HermitianEigenpairSequence.valueHyperreal
    {A : OpAlmostRepresentation G} {S : Finset G}
    (e : HermitianEigenpairSequence A S) : Hyperreal :=
  Hyperreal.ofSeq e.value

theorem HermitianEigenpairSequence.valueHyperreal_finite
    {A : OpAlmostRepresentation G} {S : Finset G}
    (e : HermitianEigenpairSequence A S) :
    0 ≤ ArchimedeanClass.mk e.valueHyperreal := by
  apply ArchimedeanClass.mk_nonneg_of_le_of_le_of_archimedean
    Hyperreal.coeRingHom (r := (-1 : ℝ)) (s := (1 : ℝ))
  · change Hyperreal.ofSeq (fun _ : ℕ ↦ (-1 : ℝ)) ≤
      Hyperreal.ofSeq e.value
    rw [Hyperreal.ofSeq_le_ofSeq]
    exact Filter.Eventually.of_forall fun n ↦
      (abs_le.mp (e.abs_value_le_one n)).1
  · change Hyperreal.ofSeq e.value ≤
      Hyperreal.ofSeq (fun _ : ℕ ↦ (1 : ℝ))
    rw [Hyperreal.ofSeq_le_ofSeq]
    exact Filter.Eventually.of_forall fun n ↦
      (abs_le.mp (e.abs_value_le_one n)).2

theorem hyperreal_pow_finite {x : Hyperreal}
    (hx : 0 ≤ ArchimedeanClass.mk x) (k : ℕ) :
    0 ≤ ArchimedeanClass.mk (x ^ k) := by
  induction k with
  | zero => simp
  | succ k ih =>
      rw [pow_succ']
      exact hyperreal_mul_finite hx ih

theorem stdPart_hyperreal_pow {x : Hyperreal}
    (hx : 0 ≤ ArchimedeanClass.mk x) (k : ℕ) :
    ArchimedeanClass.stdPart (x ^ k) =
      ArchimedeanClass.stdPart x ^ k := by
  induction k with
  | zero => simp
  | succ k ih =>
      rw [pow_succ', pow_succ', ArchimedeanClass.stdPart_mul hx
        (hyperreal_pow_finite hx k), ih]

/-- Standard part of an exact-word displacement is the scalar displacement
polynomial evaluated at the standard-part eigenvalue. -/
theorem stdPart_displacement_eq_eigenvaluePolynomial
    (S : Finset G) (hsymm : ∀ g ∈ S, g⁻¹ ∈ S)
    (A : OpAlmostRepresentation G) (e : HermitianEigenpairSequence A S)
    (k : ℕ) :
    let d := KazhdanGNS.averagingDisplacementCoefficients S k
    ArchimedeanClass.stdPart
        (combinationNormSqHyperreal A e.vector d.support id d) =
      ((ArchimedeanClass.stdPart e.valueHyperreal) ^ (k + 1) -
        (ArchimedeanClass.stdPart e.valueHyperreal) ^ k) ^ 2 := by
  let d := KazhdanGNS.averagingDisplacementCoefficients S k
  let H := combinationNormSqHyperreal A e.vector d.support id d
  let L := e.valueHyperreal
  let P := (L ^ (k + 1) - L ^ k) ^ 2
  have hHfinite : 0 ≤ ArchimedeanClass.mk H :=
    combinationNormSqHyperreal_finite A e.vector d.support id d
  have hLfinite : 0 ≤ ArchimedeanClass.mk L := e.valueHyperreal_finite
  have hLk1 := hyperreal_pow_finite hLfinite (k + 1)
  have hLk := hyperreal_pow_finite hLfinite k
  have hsubfinite : 0 ≤ ArchimedeanClass.mk (L ^ (k + 1) - L ^ k) :=
    KazhdanGNS.hyperreal_sub_finite hLk1 hLk
  have hPfinite : 0 ≤ ArchimedeanClass.mk P := by
    change 0 ≤ ArchimedeanClass.mk ((L ^ (k + 1) - L ^ k) ^ 2)
    exact hyperreal_pow_finite hsubfinite 2
  have hdiffFinite : 0 ≤ ArchimedeanClass.mk (H - P) :=
    KazhdanGNS.hyperreal_sub_finite hHfinite hPfinite
  have hHseq : H = Hyperreal.ofSeq (fun n ↦
      finiteAveragingDisplacementNormSq A n (e.vector.vec n) S k) :=
    combinationNormSqHyperreal_displacement_eq_ofSeq A e.vector S k
  have hPseq : P = Hyperreal.ofSeq (fun n ↦
      (e.value n ^ (k + 1) - e.value n ^ k) ^ 2) := by
    change (ofSeqRingHom e.value ^ (k + 1) - ofSeqRingHom e.value ^ k) ^ 2 =
      ofSeqRingHom (fun n ↦ (e.value n ^ (k + 1) - e.value n ^ k) ^ 2)
    rw [← map_pow, ← map_pow, ← map_sub, ← map_pow]
    congr 1
  have hsmall : 0 < ArchimedeanClass.mk (H - P) := by
    rw [hHseq, hPseq]
    change 0 < ArchimedeanClass.mk (Hyperreal.ofSeq (fun n ↦
      finiteAveragingDisplacementNormSq A n (e.vector.vec n) S k -
        (e.value n ^ (k + 1) - e.value n ^ k) ^ 2))
    apply Hyperreal.archimedeanClassMk_pos_of_tendsto
    rw [Hyperreal.tendsto_ofSeq]
    exact (eigen_displacementNormSq_sub_scalar_tendsto_zero
      A S hsymm e k).mono_left Nat.hyperfilter_le_atTop
  have hzero : ArchimedeanClass.stdPart (H - P) = 0 :=
    ArchimedeanClass.stdPart_eq_zero.mpr hsmall.ne'
  have hsub := ArchimedeanClass.stdPart_sub hHfinite hPfinite
  rw [hzero] at hsub
  have hHP : ArchimedeanClass.stdPart H = ArchimedeanClass.stdPart P :=
    sub_eq_zero.mp hsub.symm
  change ArchimedeanClass.stdPart H =
    ((ArchimedeanClass.stdPart L) ^ (k + 1) -
      (ArchimedeanClass.stdPart L) ^ k) ^ 2
  rw [hHP]
  change ArchimedeanClass.stdPart ((L ^ (k + 1) - L ^ k) ^ 2) = _
  rw [stdPart_hyperreal_pow hsubfinite 2,
    ArchimedeanClass.stdPart_sub hLk1 hLk,
    stdPart_hyperreal_pow hLfinite (k + 1),
    stdPart_hyperreal_pow hLfinite k]

/-- No eigenvalue of the Hermitian weak-MF average can persist in a closed
band strictly between the Kazhdan moving-spectrum bound and `1`. -/
theorem hermitianAverage_eventually_no_intermediate_eigenvalues :
    ∀ {G : Type} [Group G]
      {Q : Finset G} {ε : ℝ} (_hQ : IsKazhdanPair.{0, 0} G Q ε)
      (S : Finset G) (_hQS : Q ⊆ S) (_hone : 1 ∈ S) (_hεone : ε ≤ 1)
      (_hsymm : ∀ g ∈ S, g⁻¹ ∈ S)
      (A : OpAlmostRepresentation G) {a b : ℝ}
      (_ha : 1 - ε ^ 2 / (4 * S.card) < a) (_hb : b < 1),
      ∃ N : ℕ, ∀ n ≥ N, ∀ i : A.model n,
        ¬ (a ≤ Matrix.IsHermitian.eigenvalues
            (hermitianAverage_conjTranspose A S n) i ∧
          Matrix.IsHermitian.eigenvalues
            (hermitianAverage_conjTranspose A S n) i ≤ b) := by
  intro G _ Q ε hQ S hQS hone hεone hsymm A a b ha hb
  classical
  by_contra h
  push Not at h
  choose φ hφ i hai hib using h
  let B := A.reindex φ hφ
  let hH : ∀ n, (hermitianAverage B S n).IsHermitian := fun n ↦
    hermitianAverage_conjTranspose B S n
  let e : HermitianEigenpairSequence B S := {
    vector := {
      vec := fun n ↦ (hH n).eigenvectorBasis (i n)
      norm_eq_one := fun n ↦ (hH n).eigenvectorBasis.orthonormal.1 (i n) }
    value := fun n ↦ (hH n).eigenvalues (i n)
    eigen := by
      intro n
      apply PiLp.ext
      intro j
      exact congrFun ((hH n).mulVec_eigenvectorBasis (i n)) j
    }
  let L := e.valueHyperreal
  let ell : ℝ := ArchimedeanClass.stdPart L
  have hLfinite : 0 ≤ ArchimedeanClass.mk L := e.valueHyperreal_finite
  have haPoint : ∀ n, a ≤ e.value n := by
    intro n
    exact hai n
  have hbPoint : ∀ n, e.value n ≤ b := by
    intro n
    exact hib n
  have haHyper : ((a : ℝ) : Hyperreal) ≤ L := by
    change Hyperreal.ofSeq (fun _ : ℕ ↦ a) ≤ Hyperreal.ofSeq e.value
    rw [Hyperreal.ofSeq_le_ofSeq]
    exact Filter.Eventually.of_forall haPoint
  have hbHyper : L ≤ ((b : ℝ) : Hyperreal) := by
    change Hyperreal.ofSeq e.value ≤ Hyperreal.ofSeq (fun _ : ℕ ↦ b)
    rw [Hyperreal.ofSeq_le_ofSeq]
    exact Filter.Eventually.of_forall hbPoint
  have haell : a ≤ ell :=
    ArchimedeanClass.le_stdPart_of_le Hyperreal.coeRingHom hLfinite haHyper
  have hellb : ell ≤ b :=
    ArchimedeanClass.stdPart_le_of_le Hyperreal.coeRingHom hLfinite hbHyper
  have hcontract := stdPart_averagingDisplacementNormSq_le
    hQ S hQS hone hεone B e.vector 1
  have hpoly1 := stdPart_displacement_eq_eigenvaluePolynomial
    S hsymm B e 1
  have hpoly0 := stdPart_displacement_eq_eigenvaluePolynomial
    S hsymm B e 0
  dsimp only at hcontract hpoly1 hpoly0
  rw [hpoly1, hpoly0] at hcontract
  have hcontract' : (ell ^ 2 - ell) ^ 2 ≤
      (1 - ε ^ 2 / (4 * S.card)) ^ 2 * (ell ^ 1 - ell ^ 0) ^ 2 := by
    simpa [ell, L] using hcontract
  have hcardNat : 0 < S.card := Finset.card_pos.mpr ⟨1, hone⟩
  have hcard : (0 : ℝ) < S.card := by exact_mod_cast hcardNat
  have hεsq : ε ^ 2 ≤ 1 := by
    nlinarith [sq_nonneg ε, hQ.1, hεone]
  have hdenOne : (1 : ℝ) ≤ 4 * S.card := by
    have : (1 : ℝ) ≤ S.card := by exact_mod_cast hcardNat
    nlinarith
  have hc0 : 0 ≤ 1 - ε ^ 2 / (4 * S.card) := by
    rw [sub_nonneg, div_le_one (by positivity)]
    exact hεsq.trans hdenOne
  have helllt : ell < 1 := hellb.trans_lt hb
  have hcell : 1 - ε ^ 2 / (4 * S.card) < ell := ha.trans_le haell
  have hne : 0 < (ell - 1) ^ 2 := sq_pos_of_ne_zero (by linarith)
  have hsquares : ell ^ 2 ≤
      (1 - ε ^ 2 / (4 * S.card)) ^ 2 := by
    have hfactor : (ell ^ 2 - ell) ^ 2 = ell ^ 2 * (ell - 1) ^ 2 := by ring
    have hfactor0 : (ell ^ 1 - ell ^ 0) ^ 2 = (ell - 1) ^ 2 := by ring
    rw [hfactor, hfactor0] at hcontract'
    nlinarith
  nlinarith

/-! ## The explicit estimate downstream of the one non-effective step

The `∃ N` above is the only non-effective ingredient of the manuscript's
finite-stage proof.  Past it, the appendix's displacement estimate holds at
each single coordinate with the printed constant `√(2|S|δ)`, by the
ultrafilter-free argument of
`GroupApproximation/Sofic/FiniteStageRobustGap.lean`. -/

/-- **The appendix's estimate (i), assembled.**  Beyond a single
(non-effective) stage `N`, every unit eigenvector of the Hermitian average
whose eigenvalue is retained by the threshold `θ` is displaced by each
generator by at most the explicit amount `√(2|S|δ)`; the eigenvalue band
comes from `hermitianAverage_eventually_no_intermediate_eigenvalues` and the
constant from `FiniteStageRobustGap.norm_act_sub_sq_le_of_eigenvector`. -/
theorem hermitianAverage_eventually_eigenvector_displacement_le
    {Q : Finset G} {ε : ℝ} (hQ : IsKazhdanPair.{0, 0} G Q ε)
    (S : Finset G) (hQS : Q ⊆ S) (hone : 1 ∈ S) (hεone : ε ≤ 1)
    (hsymm : ∀ g ∈ S, g⁻¹ ∈ S) (A : OpAlmostRepresentation G) {θ δ : ℝ}
    (hθ : 1 - ε ^ 2 / (4 * S.card) < θ) (hδ : 0 < δ) :
    ∃ N : ℕ, ∀ n ≥ N, ∀ i : A.model n,
      θ ≤ Matrix.IsHermitian.eigenvalues
          (hermitianAverage_conjTranspose A S n) i →
        ∀ g ∈ S,
          ‖FiniteStageRobustGap.act A n g
              (Matrix.IsHermitian.eigenvectorBasis
                (hermitianAverage_conjTranspose A S n) i) -
            Matrix.IsHermitian.eigenvectorBasis
              (hermitianAverage_conjTranspose A S n) i‖ ≤
            Real.sqrt (2 * (S.card : ℝ) * δ) := by
  have hS : S.Nonempty := ⟨1, hone⟩
  obtain ⟨N, hN⟩ :=
    hermitianAverage_eventually_no_intermediate_eigenvalues hQ S hQS hone
      hεone hsymm A hθ (show 1 - δ < 1 by linarith)
  refine ⟨N, fun n hn i hi g hg ↦ ?_⟩
  have hHerm : (hermitianAverage A S n).IsHermitian :=
    hermitianAverage_conjTranspose A S n
  have hv : ‖hHerm.eigenvectorBasis i‖ = 1 :=
    hHerm.eigenvectorBasis.orthonormal.1 i
  have heig : FiniteStageRobustGap.applyMat (hermitianAverage A S n)
      (hHerm.eigenvectorBasis i) =
      ((hHerm.eigenvalues i : ℝ) : ℂ) • hHerm.eigenvectorBasis i := by
    apply PiLp.ext
    intro j
    exact congrFun (hHerm.mulVec_eigenvectorBasis i) j
  have hband : 1 - δ < hHerm.eigenvalues i := by
    by_contra hcon
    push Not at hcon
    exact hN n hn i ⟨hi, hcon⟩
  have hsq := FiniteStageRobustGap.norm_act_sub_sq_le_of_eigenvector
    A S n hS hv heig hg
  have hcard : (0 : ℝ) ≤ 2 * (S.card : ℝ) := by positivity
  have hstep : 2 * (S.card : ℝ) * (1 - hHerm.eigenvalues i) ≤
      2 * (S.card : ℝ) * δ :=
    mul_le_mul_of_nonneg_left (by linarith) hcard
  have hroot := Real.sqrt_le_sqrt (hsq.trans hstep)
  rwa [Real.sqrt_sq (norm_nonneg _)] at hroot

end WeakMFVectorGNS
end GroupApproximation
