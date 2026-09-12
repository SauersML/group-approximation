import GroupApproximation.Analysis.AntipodalBlockOffDiagonal
import GroupApproximation.Analysis.AntipodalBlockWitness
import GroupApproximation.Analysis.AntipodalBlockNontrivial
import GroupApproximation.Analysis.UniformTracialGNSTwoGauge
import GroupApproximation.Analysis.CuntzPedersenTraceZero
import Mathlib.Data.Matrix.Basis

/-!
# The antipodal-block witness is uniformly trace-two-null

This file proves the trace calculation needed by the STW XXII counterexample
without classifying traces on the homogeneous blocks.  The coordinate
functions of the sphere give explicit lower-left matrix sections.  Summing
their self-commutators over the sphere coordinates and over the tautological
coordinates gives the diagonal witness, up to the scalar `1 / s`.  Therefore
every tracial state kills the witness directly from traciality.

The resulting elementary equation determines the trace of the distinguished
projection and hence the squared trace two-norm of the witness.  No measure
representation theorem or irreducible-representation classification enters.
-/

namespace GroupApproximation
namespace STW22

open GroupApproximation.ThirdParty.HamSandwich.SphereOddDegree
open UniformTracialGNSTwoGauge

open scoped CStarAlgebra ComplexOrder Matrix InnerProductSpace

noncomputable section

/-- The real `r`-th coordinate on the unit sphere, regarded as a complex
continuous function. -/
def sphereCoordinate (d : ℕ) (r : Fin (d + 1)) : C(Sphere d, ℂ) where
  toFun x := ((EuclideanSpace.proj r x.1 : ℝ) : ℂ)
  continuous_toFun := Complex.continuous_ofReal.comp
    ((EuclideanSpace.proj r).continuous.comp continuous_subtype_val)

@[simp]
theorem sphereCoordinate_apply (d : ℕ) (r : Fin (d + 1)) (x : Sphere d) :
    sphereCoordinate d r x = ((EuclideanSpace.proj r x.1 : ℝ) : ℂ) :=
  rfl

@[simp]
theorem sphereCoordinate_neg (d : ℕ) (r : Fin (d + 1)) (x : Sphere d) :
    sphereCoordinate d r (-x) = -sphereCoordinate d r x := by
  simp [sphereCoordinate]

/-- The squared sphere coordinates sum to one, in complex scalars. -/
theorem sum_sphereCoordinate_mul_self (d : ℕ) (x : Sphere d) :
    ∑ r : Fin (d + 1), sphereCoordinate d r x * sphereCoordinate d r x = 1 := by
  have hxnorm : ‖(x.1 : EuclideanSpace ℝ (Fin (d + 1)))‖ = 1 := by
    have hx := x.2
    rw [Metric.mem_sphere, dist_zero_right] at hx
    exact hx
  calc
    ∑ r : Fin (d + 1), sphereCoordinate d r x * sphereCoordinate d r x =
        ((∑ r : Fin (d + 1), (EuclideanSpace.proj r x.1) ^ 2 : ℝ) : ℂ) := by
          push_cast
          simp only [sphereCoordinate_apply, pow_two]
    _ = ((‖(x.1 : EuclideanSpace ℝ (Fin (d + 1)))‖ ^ 2 : ℝ) : ℂ) := by
          congr 1
          rw [EuclideanSpace.real_norm_sq_eq]
          apply Finset.sum_congr rfl
          intro r _
          rfl
    _ = 1 := by rw [hxnorm]; norm_num

/-- A matrix with one lower-left entry. -/
def lowerLeftMatrix (s : ℕ) (i : Fin s) (z : ℂ) :
    CStarMatrix (Fin (s + 1)) (Fin (s + 1)) ℂ :=
  z • CStarMatrix.ofMatrix (Matrix.single i.succ 0 1)

@[simp]
theorem lowerLeftMatrix_apply (s : ℕ) (i : Fin s) (z : ℂ)
    (a b : Fin (s + 1)) :
    lowerLeftMatrix s i z a b = if i.succ = a ∧ 0 = b then z else 0 := by
  simp [lowerLeftMatrix, Matrix.single_apply]

@[simp]
theorem star_lowerLeftMatrix (s : ℕ) (i : Fin s) (z : ℂ) :
    star (lowerLeftMatrix s i z) =
      CStarMatrix.ofMatrix (Matrix.single 0 i.succ (star z)) := by
  apply CStarMatrix.ext
  intro a b
  by_cases h : i.succ = b ∧ 0 = a
  · rcases h with ⟨rfl, rfl⟩
    simp [lowerLeftMatrix, CStarMatrix.star_apply]
  · have h' : ¬(0 = a ∧ i.succ = b) := fun h' ↦ h ⟨h'.2, h'.1⟩
    simp [lowerLeftMatrix, CStarMatrix.star_apply, h, h']

theorem star_lowerLeftMatrix_mul (s : ℕ) (i : Fin s) (z : ℂ) :
    star (lowerLeftMatrix s i z) * lowerLeftMatrix s i z =
      CStarMatrix.ofMatrix (Matrix.single 0 0 (star z * z)) := by
  rw [star_lowerLeftMatrix]
  rw [show lowerLeftMatrix s i z =
    CStarMatrix.ofMatrix (Matrix.single i.succ 0 z) by
      ext a b
      simp [lowerLeftMatrix_apply, Matrix.single_apply]]
  change Matrix.single 0 i.succ (star z) * Matrix.single i.succ 0 z =
    Matrix.single 0 0 (star z * z)
  exact Matrix.single_mul_single_same (star z) 0 i.succ 0 z

theorem lowerLeftMatrix_mul_star (s : ℕ) (i : Fin s) (z : ℂ) :
    lowerLeftMatrix s i z * star (lowerLeftMatrix s i z) =
      CStarMatrix.ofMatrix (Matrix.single i.succ i.succ (z * star z)) := by
  rw [star_lowerLeftMatrix]
  rw [show lowerLeftMatrix s i z =
    CStarMatrix.ofMatrix (Matrix.single i.succ 0 z) by
      ext a b
      simp [lowerLeftMatrix_apply, Matrix.single_apply]]
  change Matrix.single i.succ 0 z * Matrix.single 0 i.succ (star z) =
    Matrix.single i.succ i.succ (z * star z)
  exact Matrix.single_mul_single_same z i.succ 0 i.succ (star z)

/-- The covariant lower-left section whose only nonzero entry is the `r`-th
sphere coordinate in row `i+1`. -/
def coordinateLowerSection (d s : ℕ) (i : Fin s) (r : Fin (d + 1)) :
    RealProjectiveBlock d s := by
  let f : SphereMatrixFunctions d s :=
    { toFun := fun x ↦ lowerLeftMatrix s i (sphereCoordinate d r x)
      continuous_toFun :=
        (sphereCoordinate d r).continuous.smul continuous_const }
  refine ⟨f, ?_⟩
  intro x
  apply CStarMatrix.ext
  intro a b
  rw [blockInvolution_conjugation_apply]
  by_cases h : i.succ = a ∧ 0 = b
  · rcases h with ⟨rfl, rfl⟩
    simp [f, lowerLeftMatrix_apply, blockSign]
  · simp [f, lowerLeftMatrix_apply, h]

@[simp]
theorem coordinateLowerSection_apply (d s : ℕ) (i : Fin s) (r : Fin (d + 1))
    (x : Sphere d) (a b : Fin (s + 1)) :
    (coordinateLowerSection d s i r).1 x a b =
      if i.succ = a ∧ 0 = b then sphereCoordinate d r x else 0 := by
  simp [coordinateLowerSection, lowerLeftMatrix_apply]

/-- One tautological coordinate contributes the difference between the
distinguished rank-one projection and its own diagonal projection. -/
theorem sum_selfCommutator_coordinateLowerSection_apply
    (d s : ℕ) (i : Fin s) (x : Sphere d) :
    (∑ r : Fin (d + 1),
        CuntzPedersenCoronaObstruction.selfCommutator
          (coordinateLowerSection d s i r)).1 x =
      CStarMatrix.ofMatrix
        (Matrix.single 0 0 1 - Matrix.single i.succ i.succ 1) := by
  change antipodalBlockEval d s x
    (∑ r : Fin (d + 1), CuntzPedersenCoronaObstruction.selfCommutator
      (coordinateLowerSection d s i r)) = _
  rw [map_sum]
  change (∑ r : Fin (d + 1),
    CuntzPedersenCoronaObstruction.selfCommutator
      (lowerLeftMatrix s i (sphereCoordinate d r x))) = _
  simp_rw [CuntzPedersenCoronaObstruction.selfCommutator_apply,
    star_lowerLeftMatrix_mul, lowerLeftMatrix_mul_star]
  change (∑ r : Fin (d + 1),
      (Matrix.single 0 0
        (star (sphereCoordinate d r x) * sphereCoordinate d r x) -
      Matrix.single i.succ i.succ
        (sphereCoordinate d r x * star (sphereCoordinate d r x)))) =
    Matrix.single 0 0 1 - Matrix.single i.succ i.succ 1
  rw [Finset.sum_sub_distrib]
  apply Matrix.ext
  intro a b
  simp only [Matrix.sum_apply, Matrix.sub_apply, Matrix.single_apply]
  have hstar : ∀ r : Fin (d + 1), star (sphereCoordinate d r x) =
      sphereCoordinate d r x := by
    intro r
    simp [sphereCoordinate]
  simp_rw [hstar]
  by_cases h00 : 0 = a ∧ 0 = b
  · rcases h00 with ⟨rfl, rfl⟩
    simpa [Fin.succ_ne_zero] using sum_sphereCoordinate_mul_self d x
  · by_cases hii : i.succ = a ∧ i.succ = b
    · rcases hii with ⟨rfl, rfl⟩
      have h0succ : (0 : Fin (s + 1)) ≠ i.succ := Ne.symm (Fin.succ_ne_zero i)
      simpa [h0succ, Fin.succ_ne_zero] using
        congrArg Neg.neg (sum_sphereCoordinate_mul_self d x)
    · simp [h00, hii]

/-- The polynomial projection `(1+u)/2` is literally the first diagonal
matrix unit. -/
theorem trivialProjectionMatrix_eq_single (s : ℕ) :
    trivialProjectionMatrix s =
      CStarMatrix.ofMatrix (Matrix.single 0 0 (1 : ℂ)) := by
  classical
  apply CStarMatrix.ext
  intro a b
  by_cases hab : a = b
  · subst b
    by_cases ha : a = 0
    · subst a
      simp [trivialProjectionMatrix, blockInvolution, blockSign,
        CStarMatrix.one_apply_eq]
      norm_num
    · have h0a : ¬(0 : Fin (s + 1)) = a := Ne.symm ha
      simp [trivialProjectionMatrix, blockInvolution, blockSign,
        CStarMatrix.one_apply_eq, ha, h0a]
  · have hzero : ¬((0 : Fin (s + 1)) = a ∧ 0 = b) := by
      rintro ⟨rfl, rfl⟩
      exact hab rfl
    simp [trivialProjectionMatrix, blockInvolution,
      hab, hzero]

theorem blockInvolution_conj_diagonalSingle (s : ℕ) (i : Fin s) :
    blockInvolution s * CStarMatrix.ofMatrix (Matrix.single i.succ i.succ 1) *
      blockInvolution s =
        CStarMatrix.ofMatrix (Matrix.single i.succ i.succ 1) := by
  apply CStarMatrix.ext
  intro a b
  rw [blockInvolution_conjugation_apply]
  by_cases h : i.succ = a ∧ i.succ = b
  · rcases h with ⟨rfl, rfl⟩
    simp [blockSign, Fin.succ_ne_zero]
  · simp [h]

/-- The constant diagonal projection onto tautological coordinate `i`. -/
def diagonalCoordinateProjection (d s : ℕ) (i : Fin s) :
    RealProjectiveBlock d s :=
  constantCovariantElement d s
    (CStarMatrix.ofMatrix (Matrix.single i.succ i.succ 1))
    (blockInvolution_conj_diagonalSingle s i)

@[simp]
theorem diagonalCoordinateProjection_apply (d s : ℕ) (i : Fin s)
    (x : Sphere d) :
    (diagonalCoordinateProjection d s i).1 x =
      CStarMatrix.ofMatrix (Matrix.single i.succ i.succ 1) :=
  rfl

/-- The sphere-coordinate construction gives a block-internal, finite
self-commutator decomposition of `p-eᵢ`. -/
theorem sum_selfCommutator_coordinateLowerSection
    (d s : ℕ) (i : Fin s) :
    ∑ r : Fin (d + 1),
        CuntzPedersenCoronaObstruction.selfCommutator
          (coordinateLowerSection d s i r) =
      trivialProjection d s - diagonalCoordinateProjection d s i := by
  apply Subtype.ext
  apply ContinuousMap.ext
  intro x
  rw [sum_selfCommutator_coordinateLowerSection_apply]
  simp [trivialProjection, diagonalCoordinateProjection,
    trivialProjectionMatrix_eq_single]

/-- The distinguished line and all tautological diagonal lines form the
identity projection. -/
theorem trivialProjection_add_sum_diagonalCoordinateProjection
    (d s : ℕ) :
    trivialProjection d s + ∑ i : Fin s, diagonalCoordinateProjection d s i = 1 := by
  apply Subtype.ext
  apply ContinuousMap.ext
  intro x
  change antipodalBlockEval d s x
    (trivialProjection d s + ∑ i : Fin s, diagonalCoordinateProjection d s i) =
      antipodalBlockEval d s x 1
  rw [map_add, map_sum, map_one]
  rw [show antipodalBlockEval d s x (trivialProjection d s) =
      CStarMatrix.ofMatrix (Matrix.single 0 0 (1 : ℂ)) by
    simp [antipodalBlockEval_apply, trivialProjection,
      trivialProjectionMatrix_eq_single]]
  simp only [antipodalBlockEval_apply, diagonalCoordinateProjection_apply]
  let e := CStarMatrix.ofMatrixRingEquiv (n := Fin (s + 1)) (A := ℂ)
  change e (Matrix.single (0 : Fin (s + 1)) 0 (1 : ℂ)) +
      ∑ i : Fin s, e (Matrix.single i.succ i.succ (1 : ℂ)) = 1
  calc
    e (Matrix.single (0 : Fin (s + 1)) 0 (1 : ℂ)) +
        ∑ i : Fin s, e (Matrix.single i.succ i.succ (1 : ℂ)) =
      ∑ j : Fin (s + 1), e (Matrix.single j j (1 : ℂ)) :=
        (Fin.sum_univ_succ
          (f := fun j : Fin (s + 1) ↦
            e (Matrix.single j j (1 : ℂ)))).symm
    _ = e (∑ j : Fin (s + 1), Matrix.single j j (1 : ℂ)) := by
      rw [map_sum]
    _ = e 1 := congrArg e Matrix.sum_single_one
    _ = 1 := map_one e

/-- The concrete witness is the advertised affine combination of the
distinguished projection and its complement. -/
theorem blockWitness_eq_projection_formula (d s : ℕ) :
    blockWitness d s =
      trivialProjection d s - (s : ℂ)⁻¹ • (1 - trivialProjection d s) := by
  apply Subtype.ext
  apply ContinuousMap.ext
  intro x
  simp [blockWitness, witnessMatrix, trivialProjection]

/-- Every actual tracial state of the block kills the witness.  This is proved
from the explicit finite self-commutator decompositions above, not from a
classification of traces. -/
theorem tracialState_blockWitness_eq_zero
    (d s : ℕ) (hs : 0 < s) (τ : TracialState (RealProjectiveBlock d s)) :
    τ (blockWitness d s) = 0 := by
  have hdiag : ∀ i : Fin s,
      τ (trivialProjection d s) = τ (diagonalCoordinateProjection d s i) := by
    intro i
    apply sub_eq_zero.mp
    rw [← τ.map_sub, ← sum_selfCommutator_coordinateLowerSection]
    rw [map_sum τ.toLinearMap]
    exact Finset.sum_eq_zero fun r _ ↦
      CuntzPedersenTraceZero.tracialState_selfCommutator τ
        (coordinateLowerSection d s i r)
  have hone := congrArg (fun a : RealProjectiveBlock d s ↦ τ a)
    (trivialProjection_add_sum_diagonalCoordinateProjection d s)
  rw [τ.map_add, map_sum τ.toLinearMap, τ.apply_one] at hone
  simp_rw [← hdiag] at hone
  have hscalar : ((s : ℂ) + 1) * τ (trivialProjection d s) = 1 := by
    calc
      ((s : ℂ) + 1) * τ (trivialProjection d s) =
          τ (trivialProjection d s) + (s : ℂ) * τ (trivialProjection d s) := by ring
      _ = 1 := by simpa [Finset.sum_const, nsmul_eq_mul] using hone
  have hsC : (s : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hs.ne'
  have hs1C : (s : ℂ) + 1 ≠ 0 := by
    exact_mod_cast Nat.succ_ne_zero s
  have hp : τ (trivialProjection d s) = 1 / ((s : ℂ) + 1) := by
    apply (eq_div_iff hs1C).2
    simpa [mul_comm] using hscalar
  rw [blockWitness_eq_projection_formula, τ.map_sub, map_smul, τ.map_sub,
    τ.apply_one, hp]
  change 1 / ((s : ℂ) + 1) - (s : ℂ)⁻¹ *
    (1 - 1 / ((s : ℂ) + 1)) = 0
  have hone_sub :
      1 - 1 / ((s : ℂ) + 1) = (s : ℂ) / ((s : ℂ) + 1) := by
    field_simp [hs1C]
    ring
  rw [hone_sub]
  field_simp [hsC, hs1C]
  ring

@[simp]
theorem star_trivialProjection (d s : ℕ) :
    star (trivialProjection d s) = trivialProjection d s := by
  apply Subtype.ext
  apply ContinuousMap.ext
  intro x
  change antipodalBlockEval d s x (star (trivialProjection d s)) =
    antipodalBlockEval d s x (trivialProjection d s)
  rw [map_star]
  rw [show antipodalBlockEval d s x (trivialProjection d s) =
    CStarMatrix.ofMatrix (Matrix.single 0 0 (1 : ℂ)) by
      simp [trivialProjection, trivialProjectionMatrix_eq_single]]
  apply CStarMatrix.ext
  intro a b
  by_cases ha : a = 0 <;> by_cases hb : b = 0 <;>
    subst_vars <;>
    simp [CStarMatrix.star_apply, Matrix.single_apply, and_comm]

@[simp]
theorem trivialProjection_mul_self (d s : ℕ) :
    trivialProjection d s * trivialProjection d s = trivialProjection d s := by
  apply Subtype.ext
  apply ContinuousMap.ext
  intro x
  change antipodalBlockEval d s x
    (trivialProjection d s * trivialProjection d s) =
      antipodalBlockEval d s x (trivialProjection d s)
  rw [map_mul]
  rw [show antipodalBlockEval d s x (trivialProjection d s) =
    CStarMatrix.ofMatrix (Matrix.single 0 0 1) by
      simp [trivialProjection, trivialProjectionMatrix_eq_single]]
  change CStarMatrix.ofMatrix
      (Matrix.single (0 : Fin (s + 1)) 0 (1 : ℂ) * Matrix.single 0 0 1) =
    CStarMatrix.ofMatrix (Matrix.single 0 0 1)
  apply congrArg CStarMatrix.ofMatrix
  simp only [Matrix.single_mul_single_same, one_mul]

@[simp]
theorem star_blockWitness (d s : ℕ) :
    star (blockWitness d s) = blockWitness d s := by
  rw [blockWitness_eq_projection_formula, star_sub, star_smul, star_sub,
    star_one, star_trivialProjection]
  simp

private theorem affineProjection_sq {R : Type*} [Ring R] (p c : R)
    (hp : p * p = p) (hpc : p * c = c * p) :
    (p - c * (1 - p)) * (p - c * (1 - p)) =
      p + c * c * (1 - p) := by
  have hpcp : p * (c * p) = c * p := by
    rw [← mul_assoc, hpc, mul_assoc, hp]
  noncomm_ring [hp, hpc, hpcp]

/-- Exact square of the witness. -/
theorem blockWitness_star_mul_self (d s : ℕ) :
    star (blockWitness d s) * blockWitness d s =
      trivialProjection d s +
        ((s : ℂ)⁻¹ * (s : ℂ)⁻¹) • (1 - trivialProjection d s) := by
  rw [star_blockWitness, blockWitness_eq_projection_formula]
  simp only [Algebra.smul_def]
  rw [map_mul]
  let p := trivialProjection d s
  let c := algebraMap ℂ (RealProjectiveBlock d s) (s : ℂ)⁻¹
  change (p - c * (1 - p)) * (p - c * (1 - p)) =
    p + c * c * (1 - p)
  have hp : p * p = p := trivialProjection_mul_self d s
  have hpc : p * c = c * p := (Algebra.commutes (s : ℂ)⁻¹ p).symm
  exact affineProjection_sq p c hp hpc

/-- Every tracial state sees squared two-norm exactly `1/s`. -/
theorem tracialState_blockWitness_star_mul_self
    (d s : ℕ) (hs : 0 < s) (τ : TracialState (RealProjectiveBlock d s)) :
    τ (star (blockWitness d s) * blockWitness d s) = (s : ℂ)⁻¹ := by
  rw [blockWitness_star_mul_self, τ.map_add, map_smul, τ.map_sub, τ.apply_one]
  have hdiag : ∀ i : Fin s,
      τ (trivialProjection d s) = τ (diagonalCoordinateProjection d s i) := by
    intro i
    apply sub_eq_zero.mp
    rw [← τ.map_sub, ← sum_selfCommutator_coordinateLowerSection]
    rw [map_sum τ.toLinearMap]
    exact Finset.sum_eq_zero fun r _ ↦
      CuntzPedersenTraceZero.tracialState_selfCommutator τ
        (coordinateLowerSection d s i r)
  have hone := congrArg (fun a : RealProjectiveBlock d s ↦ τ a)
    (trivialProjection_add_sum_diagonalCoordinateProjection d s)
  rw [τ.map_add, map_sum τ.toLinearMap, τ.apply_one] at hone
  simp_rw [← hdiag] at hone
  have hscalar : ((s : ℂ) + 1) * τ (trivialProjection d s) = 1 := by
    calc
      ((s : ℂ) + 1) * τ (trivialProjection d s) =
          τ (trivialProjection d s) + (s : ℂ) * τ (trivialProjection d s) := by ring
      _ = 1 := by simpa [Finset.sum_const, nsmul_eq_mul] using hone
  have hsC : (s : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hs.ne'
  have hs1C : (s : ℂ) + 1 ≠ 0 := by
    exact_mod_cast Nat.succ_ne_zero s
  have hp : τ (trivialProjection d s) = 1 / ((s : ℂ) + 1) := by
    apply (eq_div_iff hs1C).2
    simpa [mul_comm] using hscalar
  rw [hp]
  change 1 / ((s : ℂ) + 1) + ((s : ℂ)⁻¹ * (s : ℂ)⁻¹) *
    (1 - 1 / ((s : ℂ) + 1)) = (s : ℂ)⁻¹
  have hone_sub :
      1 - 1 / ((s : ℂ) + 1) = (s : ℂ) / ((s : ℂ) + 1) := by
    field_simp [hs1C]
    ring
  rw [hone_sub]
  field_simp [hsC, hs1C]

/-- A concrete fibre trace, providing nonemptiness of the actual trace space. -/
def fibreTracialState (d s : ℕ) (x : Sphere d) :
    TracialState (RealProjectiveBlock d s) :=
  (Manuscript.OneSidedMFRadical.TensorSynchronizationMatrixCore.matrixTracialState
    complexTracialState (Fin (s + 1)) inferInstance).compStarAlgHom
      (antipodalBlockEval d s x)

instance nonemptyTracialState_realProjectiveBlock (d s : ℕ) :
    Nonempty (TracialState (RealProjectiveBlock d s)) :=
  ⟨fibreTracialState d s (Classical.choice (sphereNonempty d))⟩

/-- The single-state trace two-norm of the witness. -/
theorem tracialTwoNorm_blockWitness
    (d s : ℕ) (hs : 0 < s) (τ : TracialState (RealProjectiveBlock d s)) :
    tracialTwoNorm τ (blockWitness d s) = Real.sqrt ((s : ℝ)⁻¹) := by
  rw [tracialTwoNorm_def, tracialState_blockWitness_star_mul_self d s hs τ]
  norm_num

/-- A concrete family of antipodal blocks, used by the sequence completion. -/
abbrev AntipodalBlockFamily (d s : ℕ → ℕ) : ℕ → Type :=
  fun n ↦ RealProjectiveBlock (d n) (s n)

/-- The actual uniform tracial two-size of a family witness is `sqrt (1/s)`. -/
theorem tracialTwoSize_blockWitness (d s : ℕ → ℕ) (n : ℕ) (hs : 0 < s n) :
    UniformTracialSequenceCompletion.tracialTwoSize
        (D := AntipodalBlockFamily d s) n (blockWitness (d n) (s n)) =
      Real.sqrt (((s n : ℕ) : ℝ)⁻¹) := by
  rw [tracialTwoSize_eq_sSup]
  have hfun :
      (fun τ : TracialState (RealProjectiveBlock (d n) (s n)) ↦
        tracialTwoNorm τ (blockWitness (d n) (s n))) =
      fun _ ↦ Real.sqrt (((s n : ℕ) : ℝ)⁻¹) := by
    funext τ
    exact tracialTwoNorm_blockWitness (d n) (s n) hs τ
  change sSup (Set.range (fun τ : TracialState (RealProjectiveBlock (d n) (s n)) ↦
    tracialTwoNorm τ (blockWitness (d n) (s n)))) = _
  simp_rw [tracialTwoNorm_blockWitness (d n) (s n) hs]
  rw [Set.range_const, csSup_singleton]

end

end STW22
end GroupApproximation
