import GroupApproximation.Analysis.AntipodalBlockOffDiagonal
import GroupApproximation.Analysis.AntipodalBlockNontrivial
import GroupApproximation.Analysis.AntipodalBlockWitness
import GroupApproximation.Analysis.CStarC0DirectSum
import GroupApproximation.Analysis.CStarTopologicalSchur
import GroupApproximation.External.TauCeti.RepresentationTheory.Irreducible
import Mathlib.Data.Matrix.Basis

/-!
# The real-projective blocks are type I

This file proves the type-I property of `RealProjectiveBlock` directly.  The
key finite-generation observation is elementary: diagonal-block entries are
even functions, while the two off-diagonal corners are odd.  Every odd
function `f` on a sphere satisfies

`f(x) = ∑ k, x_k * (x_k * f(x))`,

and each coefficient `x_k * f(x)` is even.  Thus the block is a finite module
over its central algebra of even scalar functions.  Topological Schur makes
that center scalar in an irreducible representation, forcing the Hilbert space
to be finite-dimensional; finite-dimensional Burnside then gives surjectivity.
-/

namespace GroupApproximation
namespace STW22

open GroupApproximation.ThirdParty.HamSandwich.SphereOddDegree

noncomputable section

open scoped CStarAlgebra ComplexOrder Matrix

universe u

/-! ## Sphere-coordinate generators -/

/-- A sphere coordinate, named locally for the type-I proof so this module has
no dependency on the trace-size computation. -/
def typeISphereCoordinate (d : ℕ) (r : Fin (d + 1)) : C(Sphere d, ℂ) where
  toFun x := ((EuclideanSpace.proj r x.1 : ℝ) : ℂ)
  continuous_toFun := Complex.continuous_ofReal.comp
    ((EuclideanSpace.proj r).continuous.comp continuous_subtype_val)

@[simp]
theorem typeISphereCoordinate_apply (d : ℕ) (r : Fin (d + 1)) (x : Sphere d) :
    typeISphereCoordinate d r x = ((EuclideanSpace.proj r x.1 : ℝ) : ℂ) := rfl

@[simp]
theorem typeISphereCoordinate_neg (d : ℕ) (r : Fin (d + 1)) (x : Sphere d) :
    typeISphereCoordinate d r (-x) = -typeISphereCoordinate d r x := by
  simp [typeISphereCoordinate]

theorem sum_typeISphereCoordinate_mul_self (d : ℕ) (x : Sphere d) :
    ∑ r : Fin (d + 1), typeISphereCoordinate d r x * typeISphereCoordinate d r x = 1 := by
  have hxnorm : ‖(x.1 : EuclideanSpace ℝ (Fin (d + 1)))‖ = 1 := by
    have hx := x.2
    rw [Metric.mem_sphere, dist_zero_right] at hx
    exact hx
  calc
    ∑ r : Fin (d + 1), typeISphereCoordinate d r x * typeISphereCoordinate d r x =
        ((∑ r : Fin (d + 1), (EuclideanSpace.proj r x.1) ^ 2 : ℝ) : ℂ) := by
          push_cast
          simp only [typeISphereCoordinate_apply, pow_two]
    _ = ((‖(x.1 : EuclideanSpace ℝ (Fin (d + 1)))‖ ^ 2 : ℝ) : ℂ) := by
          congr 1
          rw [EuclideanSpace.real_norm_sq_eq]
          apply Finset.sum_congr rfl
          intro r _
          rfl
    _ = 1 := by rw [hxnorm]; norm_num

theorem sum_typeISphereCoordinate_mul (d : ℕ) (x : Sphere d) (z : ℂ) :
    ∑ r : Fin (d + 1),
      (typeISphereCoordinate d r x * z) * typeISphereCoordinate d r x = z := by
  calc
    ∑ r : Fin (d + 1),
        (typeISphereCoordinate d r x * z) * typeISphereCoordinate d r x =
        z * ∑ r : Fin (d + 1),
          typeISphereCoordinate d r x * typeISphereCoordinate d r x := by
            rw [Finset.mul_sum]
            apply Finset.sum_congr rfl
            intro r _
            ring
    _ = z := by rw [sum_typeISphereCoordinate_mul_self]; simp

@[simp]
theorem sum_sphereCoordinate_apply_mul (d : ℕ) (x : Sphere d) (z : ℂ) :
    ∑ r : Fin (d + 1),
      (((EuclideanSpace.proj r x.1 : ℝ) : ℂ) * z) *
        ((EuclideanSpace.proj r x.1 : ℝ) : ℂ) = z := by
  simpa only [typeISphereCoordinate_apply] using sum_typeISphereCoordinate_mul d x z

/-- A lower-left matrix unit weighted by a sphere coordinate. -/
def typeICoordinateLowerSection (d s : ℕ) (i : Fin s) (r : Fin (d + 1)) :
    RealProjectiveBlock d s := by
  let f : SphereMatrixFunctions d s :=
    { toFun := fun x ↦ typeISphereCoordinate d r x •
        CStarMatrix.ofMatrix (Matrix.single i.succ 0 1)
      continuous_toFun := (typeISphereCoordinate d r).continuous.smul continuous_const }
  refine ⟨f, ?_⟩
  intro x
  apply CStarMatrix.ext
  intro a b
  rw [blockInvolution_conjugation_apply]
  by_cases h : i.succ = a ∧ 0 = b
  · rcases h with ⟨rfl, rfl⟩
    simp [f, blockSign]
  · simp [f, h]

@[simp]
theorem typeICoordinateLowerSection_apply (d s : ℕ) (i : Fin s) (r : Fin (d + 1))
    (x : Sphere d) (a b : Fin (s + 1)) :
    (typeICoordinateLowerSection d s i r).1 x a b =
      if i.succ = a ∧ 0 = b then typeISphereCoordinate d r x else 0 := by
  simp [typeICoordinateLowerSection, Matrix.single_apply]

/-- The matching upper-right coordinate section. -/
def typeICoordinateUpperSection (d s : ℕ) (i : Fin s) (r : Fin (d + 1)) :
    RealProjectiveBlock d s := by
  let f : SphereMatrixFunctions d s :=
    { toFun := fun x ↦ typeISphereCoordinate d r x •
        CStarMatrix.ofMatrix (Matrix.single 0 i.succ 1)
      continuous_toFun := (typeISphereCoordinate d r).continuous.smul continuous_const }
  refine ⟨f, ?_⟩
  intro x
  apply CStarMatrix.ext
  intro a b
  rw [blockInvolution_conjugation_apply]
  by_cases h : 0 = a ∧ i.succ = b
  · rcases h with ⟨rfl, rfl⟩
    simp [f, blockSign]
  · simp [f, h]

@[simp]
theorem typeICoordinateUpperSection_apply (d s : ℕ) (i : Fin s) (r : Fin (d + 1))
    (x : Sphere d) (a b : Fin (s + 1)) :
    (typeICoordinateUpperSection d s i r).1 x a b =
      if 0 = a ∧ i.succ = b then typeISphereCoordinate d r x else 0 := by
  simp [typeICoordinateUpperSection, Matrix.single_apply]

/-! ## Central even scalar sections -/

/-- An even scalar function, embedded as scalar matrices in the projective
block. -/
def evenScalarElement {d s : ℕ} (c : C(Sphere d, ℂ))
    (hc : ∀ x : Sphere d, c (-x) = c x) : RealProjectiveBlock d s := by
  let f : SphereMatrixFunctions d s :=
    { toFun := fun x ↦ c x • 1
      continuous_toFun := c.continuous.smul continuous_const }
  refine ⟨f, ?_⟩
  intro x
  change c (-x) • (1 : CStarMatrix (Fin (s + 1)) (Fin (s + 1)) ℂ) =
    blockInvolution s * (c x • 1) * blockInvolution s
  rw [hc]
  simp only [mul_smul_comm, smul_mul_assoc, mul_one]
  rw [blockInvolution_sq]

@[simp]
theorem evenScalarElement_apply {d s : ℕ} (c : C(Sphere d, ℂ))
    (hc : ∀ x : Sphere d, c (-x) = c x) (x : Sphere d) :
    (evenScalarElement (s := s) c hc).1 x = c x • 1 := rfl

/-- Scalar sections are central in the block. -/
theorem evenScalarElement_mul_comm {d s : ℕ} (c : C(Sphere d, ℂ))
    (hc : ∀ x : Sphere d, c (-x) = c x) (a : RealProjectiveBlock d s) :
    evenScalarElement (s := s) c hc * a = a * evenScalarElement (s := s) c hc := by
  apply Subtype.ext
  apply ContinuousMap.ext
  intro x
  change (c x • 1) * a.1 x = a.1 x * (c x • 1)
  simp

/-! ## A finite family of fixed covariant generators -/

/-- The constant matrix unit at the distinguished `(0,0)` entry. -/
def distinguishedMatrixUnit (d s : ℕ) : RealProjectiveBlock d s :=
  constantCovariantElement d s
    (CStarMatrix.ofMatrix (Matrix.single 0 0 1)) (by
      apply CStarMatrix.ext
      intro a b
      rw [blockInvolution_conjugation_apply]
      by_cases h : 0 = a ∧ 0 = b
      · rcases h with ⟨rfl, rfl⟩
        simp [blockSign]
      · simp [h])

@[simp]
theorem distinguishedMatrixUnit_apply (d s : ℕ) (x : Sphere d)
    (a b : Fin (s + 1)) :
    (distinguishedMatrixUnit d s).1 x a b = if 0 = a ∧ 0 = b then 1 else 0 := by
  simp [distinguishedMatrixUnit, Matrix.single_apply]

/-- Constant matrix units inside the lower-right `s × s` block. -/
def lowerBlockMatrixUnit (d s : ℕ) (i j : Fin s) : RealProjectiveBlock d s :=
  constantCovariantElement d s
    (CStarMatrix.ofMatrix (Matrix.single i.succ j.succ 1)) (by
      apply CStarMatrix.ext
      intro a b
      rw [blockInvolution_conjugation_apply]
      by_cases h : i.succ = a ∧ j.succ = b
      · rcases h with ⟨rfl, rfl⟩
        simp [blockSign]
      · simp [h])

@[simp]
theorem lowerBlockMatrixUnit_apply (d s : ℕ) (i j : Fin s) (x : Sphere d)
    (a b : Fin (s + 1)) :
    (lowerBlockMatrixUnit d s i j).1 x a b =
      if i.succ = a ∧ j.succ = b then 1 else 0 := by
  simp [lowerBlockMatrixUnit, Matrix.single_apply]

/-! ## Even coefficient functions -/

def distinguishedCoefficient {d s : ℕ} (a : RealProjectiveBlock d s) :
    C(Sphere d, ℂ) := (matrixEntryMap 0 0).comp a.1

@[simp]
theorem distinguishedCoefficient_apply {d s : ℕ} (a : RealProjectiveBlock d s)
    (x : Sphere d) : distinguishedCoefficient a x = a.1 x 0 0 := rfl

theorem distinguishedCoefficient_neg {d s : ℕ} (a : RealProjectiveBlock d s)
    (x : Sphere d) : distinguishedCoefficient a (-x) = distinguishedCoefficient a x := by
  rw [distinguishedCoefficient_apply, distinguishedCoefficient_apply,
    realProjectiveBlock_entry_neg]
  simp [blockSign]

def lowerBlockCoefficient {d s : ℕ} (a : RealProjectiveBlock d s) (i j : Fin s) :
    C(Sphere d, ℂ) := (matrixEntryMap i.succ j.succ).comp a.1

@[simp]
theorem lowerBlockCoefficient_apply {d s : ℕ} (a : RealProjectiveBlock d s)
    (i j : Fin s) (x : Sphere d) : lowerBlockCoefficient a i j x = a.1 x i.succ j.succ := rfl

theorem lowerBlockCoefficient_neg {d s : ℕ} (a : RealProjectiveBlock d s)
    (i j : Fin s) (x : Sphere d) :
    lowerBlockCoefficient a i j (-x) = lowerBlockCoefficient a i j x := by
  rw [lowerBlockCoefficient_apply, lowerBlockCoefficient_apply,
    realProjectiveBlock_entry_neg]
  simp [blockSign]

/-- The even coefficient `x_r * a_{i,0}(x)` attached to a lower-left
coordinate generator. -/
def lowerCoordinateCoefficient {d s : ℕ} (a : RealProjectiveBlock d s)
    (i : Fin s) (r : Fin (d + 1)) : C(Sphere d, ℂ) :=
  typeISphereCoordinate d r * offDiagonalColumnEntry a i

@[simp]
theorem lowerCoordinateCoefficient_apply {d s : ℕ} (a : RealProjectiveBlock d s)
    (i : Fin s) (r : Fin (d + 1)) (x : Sphere d) :
    lowerCoordinateCoefficient a i r x = typeISphereCoordinate d r x * a.1 x i.succ 0 := rfl

theorem lowerCoordinateCoefficient_neg {d s : ℕ} (a : RealProjectiveBlock d s)
    (i : Fin s) (r : Fin (d + 1)) (x : Sphere d) :
    lowerCoordinateCoefficient a i r (-x) = lowerCoordinateCoefficient a i r x := by
  change typeISphereCoordinate d r (-x) * offDiagonalColumnEntry a i (-x) =
    typeISphereCoordinate d r x * offDiagonalColumnEntry a i x
  rw [typeISphereCoordinate_neg, offDiagonalColumnEntry_neg]
  ring

/-- The even coefficient `x_r * a_{0,i}(x)` attached to an upper-right
coordinate generator. -/
def upperCoordinateCoefficient {d s : ℕ} (a : RealProjectiveBlock d s)
    (i : Fin s) (r : Fin (d + 1)) : C(Sphere d, ℂ) :=
  typeISphereCoordinate d r * offDiagonalRowEntry a i

@[simp]
theorem upperCoordinateCoefficient_apply {d s : ℕ} (a : RealProjectiveBlock d s)
    (i : Fin s) (r : Fin (d + 1)) (x : Sphere d) :
    upperCoordinateCoefficient a i r x = typeISphereCoordinate d r x * a.1 x 0 i.succ := rfl

theorem upperCoordinateCoefficient_neg {d s : ℕ} (a : RealProjectiveBlock d s)
    (i : Fin s) (r : Fin (d + 1)) (x : Sphere d) :
    upperCoordinateCoefficient a i r (-x) = upperCoordinateCoefficient a i r x := by
  change typeISphereCoordinate d r (-x) * offDiagonalRowEntry a i (-x) =
    typeISphereCoordinate d r x * offDiagonalRowEntry a i x
  rw [typeISphereCoordinate_neg, offDiagonalRowEntry_neg]
  ring

/-! ## The finite central expansion -/

/-- The explicit expansion of a block section over its central even scalar
functions. -/
def finiteCentralExpansion {d s : ℕ} (a : RealProjectiveBlock d s) :
    RealProjectiveBlock d s :=
  evenScalarElement (s := s) (distinguishedCoefficient a)
      (distinguishedCoefficient_neg a) * distinguishedMatrixUnit d s +
    (∑ i : Fin s, ∑ j : Fin s,
      evenScalarElement (s := s) (lowerBlockCoefficient a i j)
        (lowerBlockCoefficient_neg a i j) * lowerBlockMatrixUnit d s i j) +
    (∑ i : Fin s, ∑ r : Fin (d + 1),
      evenScalarElement (s := s) (lowerCoordinateCoefficient a i r)
        (lowerCoordinateCoefficient_neg a i r) * typeICoordinateLowerSection d s i r) +
    (∑ i : Fin s, ∑ r : Fin (d + 1),
      evenScalarElement (s := s) (upperCoordinateCoefficient a i r)
        (upperCoordinateCoefficient_neg a i r) * typeICoordinateUpperSection d s i r)

@[simp]
theorem finsetSum_realProjectiveBlock_apply {d s : ℕ} {I : Type*}
    (t : Finset I) (f : I → RealProjectiveBlock d s) (x : Sphere d)
    (i j : Fin (s + 1)) :
    (((∑ k ∈ t, f k) : RealProjectiveBlock d s).1 x) i j =
      ∑ k ∈ t, (f k).1 x i j := by
  classical
  induction t using Finset.induction_on with
  | empty => rfl
  | @insert k t hk ih =>
      rw [Finset.sum_insert hk, Finset.sum_insert hk]
      change (f k).1 x i j + ((∑ q ∈ t, f q).1 x) i j =
        (f k).1 x i j + ∑ q ∈ t, (f q).1 x i j
      rw [ih]

@[simp]
theorem finsetSum_continuousLinearMap_apply {H : Type*} [NormedAddCommGroup H]
    [NormedSpace ℂ H] {I : Type*} (t : Finset I)
    (f : I → H →L[ℂ] H) (x : H) :
    ((∑ k ∈ t, f k) : H →L[ℂ] H) x = ∑ k ∈ t, f k x := by
  classical
  induction t using Finset.induction_on with
  | empty => rfl
  | @insert k t hk ih =>
      rw [Finset.sum_insert hk, Finset.sum_insert hk]
      change f k x + ((∑ q ∈ t, f q) : H →L[ℂ] H) x =
        f k x + ∑ q ∈ t, f q x
      rw [ih]

@[simp]
theorem finsetSum_cStarMatrix_apply {s : ℕ} {I : Type*} (t : Finset I)
    (f : I → CStarMatrix (Fin (s + 1)) (Fin (s + 1)) ℂ)
    (i j : Fin (s + 1)) :
    ((∑ k ∈ t, f k) : CStarMatrix (Fin (s + 1)) (Fin (s + 1)) ℂ) i j =
      ∑ k ∈ t, f k i j := by
  classical
  induction t using Finset.induction_on with
  | empty => rfl
  | @insert k t hk ih =>
      rw [Finset.sum_insert hk, Finset.sum_insert hk]
      change f k i j +
          ((∑ q ∈ t, f q) : CStarMatrix (Fin (s + 1)) (Fin (s + 1)) ℂ) i j =
        f k i j + ∑ q ∈ t, f q i j
      rw [ih]

set_option linter.unusedSimpArgs false in
/-- Every projective-block section is its finite central expansion. -/
theorem finiteCentralExpansion_eq {d s : ℕ} (a : RealProjectiveBlock d s) :
    finiteCentralExpansion a = a := by
  apply Subtype.ext
  apply ContinuousMap.ext
  intro x
  apply CStarMatrix.ext
  intro k l
  rcases Fin.eq_zero_or_eq_succ k with rfl | ⟨i, rfl⟩
  · rcases Fin.eq_zero_or_eq_succ l with rfl | ⟨j, rfl⟩
    · simp [finiteCentralExpansion, Finset.sum_apply, distinguishedMatrixUnit_apply,
        lowerBlockMatrixUnit_apply, typeICoordinateLowerSection_apply,
        typeICoordinateUpperSection_apply]
    · have hj0 : (0 : Fin (s + 1)) ≠ j.succ := (Fin.succ_ne_zero j).symm
      simp [finiteCentralExpansion, Finset.sum_apply, distinguishedMatrixUnit_apply,
        lowerBlockMatrixUnit_apply, typeICoordinateLowerSection_apply,
        typeICoordinateUpperSection_apply, hj0, sum_sphereCoordinate_apply_mul]
      change ∑ r : Fin (d + 1),
        (typeISphereCoordinate d r x * a.1 x 0 j.succ) *
          typeISphereCoordinate d r x = a.1 x 0 j.succ
      exact sum_typeISphereCoordinate_mul d x (a.1 x 0 j.succ)
  · rcases Fin.eq_zero_or_eq_succ l with rfl | ⟨j, rfl⟩
    · have hi0 : (0 : Fin (s + 1)) ≠ i.succ := (Fin.succ_ne_zero i).symm
      simp [finiteCentralExpansion, Finset.sum_apply, distinguishedMatrixUnit_apply,
        lowerBlockMatrixUnit_apply, typeICoordinateLowerSection_apply,
        typeICoordinateUpperSection_apply, hi0, sum_sphereCoordinate_apply_mul]
      change ∑ r : Fin (d + 1),
        (typeISphereCoordinate d r x * a.1 x i.succ 0) *
          typeISphereCoordinate d r x = a.1 x i.succ 0
      exact sum_typeISphereCoordinate_mul d x (a.1 x i.succ 0)
    · have hi0 : (0 : Fin (s + 1)) ≠ i.succ := (Fin.succ_ne_zero i).symm
      have hj0 : (0 : Fin (s + 1)) ≠ j.succ := (Fin.succ_ne_zero j).symm
      simp [finiteCentralExpansion, Finset.sum_apply, distinguishedMatrixUnit_apply,
        lowerBlockMatrixUnit_apply, typeICoordinateLowerSection_apply,
        typeICoordinateUpperSection_apply, hi0, hj0, sum_sphereCoordinate_apply_mul]
      classical
      calc
        (∑ k : Fin s, ∑ l : Fin s,
            if k = i ∧ l = j then a.1 x k.succ l.succ else 0) =
            ∑ k : Fin s, if k = i then a.1 x k.succ j.succ else 0 := by
              apply Finset.sum_congr rfl
              intro k _
              by_cases hk : k = i
              · subst k
                simp
              · simp [hk]
        _ = a.1 x i.succ j.succ := by simp

/-! ## Irreducible representations are finite-dimensional -/

/-- A finite index for the fixed module generators in the central expansion. -/
abbrev ProjectiveBlockGeneratorIndex (d s : ℕ) :=
  Unit ⊕ (Fin s × Fin s) ⊕ (Fin s × Fin (d + 1)) ⊕ (Fin s × Fin (d + 1))

def projectiveBlockGenerator (d s : ℕ) :
    ProjectiveBlockGeneratorIndex d s → RealProjectiveBlock d s
  | Sum.inl _ => distinguishedMatrixUnit d s
  | Sum.inr (Sum.inl (i, j)) => lowerBlockMatrixUnit d s i j
  | Sum.inr (Sum.inr (Sum.inl (i, r))) => typeICoordinateLowerSection d s i r
  | Sum.inr (Sum.inr (Sum.inr (i, r))) => typeICoordinateUpperSection d s i r

section Representation

variable {d s : ℕ} {H : Type} [NormedAddCommGroup H]
  [InnerProductSpace ℂ H] [CompleteSpace H]
  (π : RealProjectiveBlock d s →⋆ₐ[ℂ] (H →L[ℂ] H))

/-- The span of the finitely many fixed generator vectors at `v`. -/
def projectiveGeneratorSpan (v : H) : Submodule ℂ H :=
  Submodule.span ℂ (Set.range fun q : ProjectiveBlockGeneratorIndex d s ↦
    π (projectiveBlockGenerator d s q) v)

theorem projectiveGeneratorSpan_finiteDimensional (v : H) :
    FiniteDimensional ℂ (projectiveGeneratorSpan π v) := by
  apply FiniteDimensional.span_of_finite ℂ
  exact Set.finite_range _

theorem projectiveBlockGenerator_apply_mem (v : H)
    (q : ProjectiveBlockGeneratorIndex d s) :
    π (projectiveBlockGenerator d s q) v ∈ projectiveGeneratorSpan π v :=
  Submodule.subset_span (Set.mem_range_self q)

/-- Every orbit vector lies in the span of the fixed finite generator family.
The topological Schur lemma is used exactly here, on each even scalar
coefficient. -/
theorem rep_apply_mem_projectiveGeneratorSpan (hπ : IsIrreducibleRep π)
    (v : H) (a : RealProjectiveBlock d s) :
    π a v ∈ projectiveGeneratorSpan π v := by
  let V := projectiveGeneratorSpan π v
  have hcentral (c : C(Sphere d, ℂ)) (hc : ∀ x : Sphere d, c (-x) = c x)
      (q : ProjectiveBlockGeneratorIndex d s) :
      π (evenScalarElement (s := s) c hc * projectiveBlockGenerator d s q) v ∈ V := by
    obtain ⟨z, hz⟩ := hπ.map_center_eq_scalar (evenScalarElement (s := s) c hc)
      (evenScalarElement_mul_comm c hc)
    have hgen : π (projectiveBlockGenerator d s q) v ∈ V :=
      projectiveBlockGenerator_apply_mem π v q
    rw [map_mul]
    change (π (evenScalarElement (s := s) c hc))
      (π (projectiveBlockGenerator d s q) v) ∈ V
    have hz_apply := congrArg
      (fun T : H →L[ℂ] H ↦ T (π (projectiveBlockGenerator d s q) v)) hz
    have hz_eval : (π (evenScalarElement (s := s) c hc))
        (π (projectiveBlockGenerator d s q) v) =
        z • (π (projectiveBlockGenerator d s q) v) := by
      calc
        _ = ((algebraMap ℂ (H →L[ℂ] H)) z)
            (π (projectiveBlockGenerator d s q) v) := hz_apply
        _ = _ := by
          rw [Algebra.algebraMap_eq_smul_one]
          rfl
    rw [hz_eval]
    exact V.smul_mem z hgen
  rw [← finiteCentralExpansion_eq a]
  simp only [finiteCentralExpansion, map_add, map_sum, add_apply,
    finsetSum_continuousLinearMap_apply]
  apply Submodule.add_mem
  · apply Submodule.add_mem
    · apply Submodule.add_mem
      · simpa [projectiveBlockGenerator] using
          hcentral (distinguishedCoefficient a) (distinguishedCoefficient_neg a)
            (Sum.inl ())
      · apply Submodule.sum_mem
        intro i _
        apply Submodule.sum_mem
        intro j _
        simpa [projectiveBlockGenerator] using
          hcentral (lowerBlockCoefficient a i j) (lowerBlockCoefficient_neg a i j)
            (Sum.inr (Sum.inl (i, j)))
    · apply Submodule.sum_mem
      intro i _
      apply Submodule.sum_mem
      intro r _
      simpa [projectiveBlockGenerator] using
        hcentral (lowerCoordinateCoefficient a i r) (lowerCoordinateCoefficient_neg a i r)
          (Sum.inr (Sum.inr (Sum.inl (i, r))))
  · apply Submodule.sum_mem
    intro i _
    apply Submodule.sum_mem
    intro r _
    simpa [projectiveBlockGenerator] using
      hcentral (upperCoordinateCoefficient a i r) (upperCoordinateCoefficient_neg a i r)
        (Sum.inr (Sum.inr (Sum.inr (i, r))))

/-- An irreducible representation of a real-projective block acts on a
finite-dimensional Hilbert space. -/
theorem IsIrreducibleRep.finiteDimensional_realProjectiveBlock
    (hπ : IsIrreducibleRep π) : FiniteDimensional ℂ H := by
  obtain ⟨v, hv⟩ := hπ.exists_ne_zero
  let V := projectiveGeneratorSpan π v
  letI : FiniteDimensional ℂ V := projectiveGeneratorSpan_finiteDimensional π v
  have hVclosed : IsClosed (V : Set H) := V.closed_of_finiteDimensional
  have hVinv : ∀ a : RealProjectiveBlock d s, ∀ x ∈ V, π a x ∈ V := by
    intro a
    have hle : V ≤ Submodule.comap ((π a : H →L[ℂ] H) : H →ₗ[ℂ] H) V := by
      apply Submodule.span_le.mpr
      rintro _ ⟨q, rfl⟩
      change π a (π (projectiveBlockGenerator d s q) v) ∈ V
      rw [← mul_apply_eq_comp, ← map_mul]
      exact rep_apply_mem_projectiveGeneratorSpan π hπ v
        (a * projectiveBlockGenerator d s q)
    exact fun _ hx ↦ hle hx
  have hVne : V ≠ ⊥ := by
    intro hbot
    have hvV : v ∈ V := by
      simpa using rep_apply_mem_projectiveGeneratorSpan π hπ v (1 : RealProjectiveBlock d s)
    rw [hbot] at hvV
    exact hv ((Submodule.mem_bot ℂ).mp hvV)
  have hVtop : V = ⊤ := (hπ.2 V ⟨hVclosed, hVinv⟩).resolve_left hVne
  apply FiniteDimensional.of_surjective (V.subtype)
  intro x
  exact ⟨⟨x, hVtop.symm ▸ Submodule.mem_top⟩, rfl⟩

end Representation

/-! ## Finite-dimensional Burnside and type I -/

section Burnside

variable {d s : ℕ} {H : Type} [NormedAddCommGroup H]
  [InnerProductSpace ℂ H] [CompleteSpace H]

/-- The multiplicative-monoid representation underlying a C-star
representation. -/
def projectiveBlockMonoidRepresentation
    (π : RealProjectiveBlock d s →⋆ₐ[ℂ] (H →L[ℂ] H)) :
    Representation ℂ (RealProjectiveBlock d s) H where
  toFun a := (π a : H →L[ℂ] H).toLinearMap
  map_one' := by
    ext x
    simp
  map_mul' a b := by
    ext x
    change π (a * b) x = π a (π b x)
    rw [map_mul]
    rfl

@[simp]
theorem projectiveBlockMonoidRepresentation_apply
    (π : RealProjectiveBlock d s →⋆ₐ[ℂ] (H →L[ℂ] H))
    (a : RealProjectiveBlock d s) (x : H) :
    projectiveBlockMonoidRepresentation π a x = π a x := rfl

/-- Topological irreducibility becomes algebraic irreducibility after the
finite-dimensionality theorem. -/
theorem projectiveBlockMonoidRepresentation_isIrreducible
    (π : RealProjectiveBlock d s →⋆ₐ[ℂ] (H →L[ℂ] H))
    (hπ : IsIrreducibleRep π) [FiniteDimensional ℂ H] :
    (projectiveBlockMonoidRepresentation π).IsIrreducible := by
  let ρ := projectiveBlockMonoidRepresentation π
  change ρ.IsIrreducible
  obtain ⟨v, hv⟩ := hπ.exists_ne_zero
  letI : Nontrivial H := ⟨⟨v, 0, hv⟩⟩
  have hbotTop : (⊥ : Subrepresentation ρ) ≠ ⊤ :=
    fun h ↦ bot_ne_top (α := Submodule ℂ H) (by
      rw [← Subrepresentation.toSubmodule_bot (ρ := ρ),
        ← Subrepresentation.toSubmodule_top (ρ := ρ), h])
  letI : Nontrivial (Subrepresentation ρ) :=
    ⟨⊥, ⊤, hbotTop⟩
  refine ⟨fun S ↦ ?_⟩
  have hclosed : IsClosed (S.toSubmodule : Set H) :=
    S.toSubmodule.closed_of_finiteDimensional
  have hinv : ∀ a : RealProjectiveBlock d s, ∀ x ∈ S.toSubmodule,
      π a x ∈ S.toSubmodule := by
    intro a x hx
    simpa [ρ] using S.apply_mem_toSubmodule a hx
  rcases hπ.2 S.toSubmodule ⟨hclosed, hinv⟩ with hbot | htop
  · left
    exact Subrepresentation.toSubmodule_injective
      (hbot.trans Subrepresentation.toSubmodule_bot.symm)
  · right
    exact Subrepresentation.toSubmodule_injective
      (htop.trans Subrepresentation.toSubmodule_top.symm)

/-- Collapse the monoid algebra of the multiplicative monoid of a complex
algebra by linearly evaluating each basis symbol at the element it names. -/
def projectiveBlockMonoidAlgebraCollapse :
    MonoidAlgebra ℂ (RealProjectiveBlock d s) →ₐ[ℂ] RealProjectiveBlock d s :=
  MonoidAlgebra.lift ℂ (RealProjectiveBlock d s) (RealProjectiveBlock d s)
    (MonoidHom.id _)

theorem projectiveBlockMonoidAlgebraCollapse_intertwines
    (π : RealProjectiveBlock d s →⋆ₐ[ℂ] (H →L[ℂ] H))
    (q : MonoidAlgebra ℂ (RealProjectiveBlock d s)) :
    (π (projectiveBlockMonoidAlgebraCollapse q) : H →L[ℂ] H).toLinearMap =
      (projectiveBlockMonoidRepresentation π).asAlgebraHom q := by
  induction q using MonoidAlgebra.induction_linear with
  | zero => simp
  | add q r hq hr => simp [hq, hr]
  | single a c =>
      ext x
      simp [projectiveBlockMonoidAlgebraCollapse,
        projectiveBlockMonoidRepresentation, Representation.asAlgebraHom_single]

/-- Every irreducible representation of a projective block is onto the full
bounded-operator algebra. -/
theorem realProjectiveBlock_irreducible_surjective
    (π : RealProjectiveBlock d s →⋆ₐ[ℂ] (H →L[ℂ] H))
    (hπ : IsIrreducibleRep π) : Function.Surjective π := by
  letI : FiniteDimensional ℂ H := hπ.finiteDimensional_realProjectiveBlock π
  let ρ := projectiveBlockMonoidRepresentation π
  have hρ : ρ.IsIrreducible := projectiveBlockMonoidRepresentation_isIrreducible π hπ
  have hsurj := Representation.asAlgebraHom_surjective_of_isIrreducible ρ hρ
  intro T
  obtain ⟨q, hq⟩ := hsurj T.toLinearMap
  refine ⟨projectiveBlockMonoidAlgebraCollapse q, ?_⟩
  apply ContinuousLinearMap.ext
  intro x
  have hcollapse := projectiveBlockMonoidAlgebraCollapse_intertwines π q
  exact LinearMap.congr_fun (hcollapse.trans hq) x

/-- The concrete real-projective homogeneous block is type I, with no
classification hypothesis on its irreducible representations. -/
theorem isTypeI_realProjectiveBlock (d s : ℕ) : IsTypeI (RealProjectiveBlock d s) := by
  intro H _ _ _ π hπ T _
  exact realProjectiveBlock_irreducible_surjective π hπ T

end Burnside

/-! ## Forgetting the unit -/

/-- A unital type-I C-star algebra is type I for the nonunital definition used
by the genuine `c₀` direct sum.  An irreducible nonunital representation of a
unital algebra automatically maps the unit to the identity: its fixed space is
a nonzero closed invariant subspace. -/
theorem IsTypeI.isTypeINonUnital {A : Type u} [CStarAlgebra A] (hA : IsTypeI A) :
    IsTypeINonUnital A := by
  intro H _ _ _ π hπ T hT
  let e : H →L[ℂ] H := π (1 : A)
  let M : Submodule ℂ H := LinearMap.ker ((1 : H →L[ℂ] H) - e : H →ₗ[ℂ] H)
  have hMclosed : IsClosed (M : Set H) := ((1 : H →L[ℂ] H) - e).isClosed_ker
  have hMinv : ∀ a : A, ∀ x ∈ M, π a x ∈ M := by
    intro a x hx
    rw [LinearMap.mem_ker] at hx ⊢
    change x - e x = 0 at hx
    change π a x - e (π a x) = 0
    have heax : e (π a x) = π a x := by
      change π 1 (π a x) = π a x
      rw [← rep_apply_mul, one_mul]
    rw [heax, sub_self]
  have hMne : M ≠ ⊥ := by
    obtain ⟨a, ha⟩ := hπ.1
    obtain ⟨x, hx⟩ : ∃ x : H, π a x ≠ 0 := by
      by_contra h
      push Not at h
      exact ha (ContinuousLinearMap.ext h)
    intro hbot
    have hmem : π a x ∈ M := by
      rw [LinearMap.mem_ker]
      change π a x - e (π a x) = 0
      change π a x - π 1 (π a x) = 0
      rw [← rep_apply_mul, one_mul, sub_self]
    rw [hbot] at hmem
    exact hx ((Submodule.mem_bot ℂ).mp hmem)
  have hMtop : M = ⊤ := (hπ.2 M hMclosed hMinv).resolve_left hMne
  have he : e = 1 := by
    apply ContinuousLinearMap.ext
    intro x
    have hx : x ∈ M := by rw [hMtop]; exact Submodule.mem_top
    rw [LinearMap.mem_ker] at hx
    change x - e x = 0 at hx
    exact (sub_eq_zero.mp hx).symm
  let πu : A →⋆ₐ[ℂ] (H →L[ℂ] H) :=
    { toFun := π
      map_one' := he
      map_mul' := map_mul π
      map_zero' := map_zero π
      map_add' := map_add π
      commutes' := by
        intro c
        rw [Algebra.algebraMap_eq_smul_one, map_smul]
        change c • e = (algebraMap ℂ (H →L[ℂ] H)) c
        rw [he]
        exact (Algebra.algebraMap_eq_smul_one c).symm
      map_star' := map_star π }
  have hπu : IsIrreducibleRep πu := by
    refine ⟨?_, ?_⟩
    · simpa [πu] using hπ.1
    intro N hN
    apply hπ.2 N hN.1
    intro a x hx
    simpa [πu] using hN.2 a x hx
  obtain ⟨a, ha⟩ := hA H πu hπu T hT
  exact ⟨a, by simpa [πu] using ha⟩

/-- The concrete blocks satisfy the nonunital type-I input of the genuine
`c₀`-sum theorem. -/
theorem isTypeINonUnital_realProjectiveBlock (d s : ℕ) :
    IsTypeINonUnital (RealProjectiveBlock d s) :=
  (isTypeI_realProjectiveBlock d s).isTypeINonUnital

/-- Any countable `c₀`-sum of the concrete real-projective blocks, followed
by ordinary unitization, is type I. -/
theorem isTypeI_unitization_c0DirectSum_realProjectiveBlocks
    (d s : ℕ → ℕ) :
    IsTypeI (Unitization ℂ
      (CStarC0DirectSum.C0DirectSum (fun n ↦ RealProjectiveBlock (d n) (s n)))) :=
  CStarC0DirectSum.isTypeI_unitization_c0DirectSum
    (D := fun n ↦ RealProjectiveBlock (d n) (s n))
    (fun n ↦ isTypeINonUnital_realProjectiveBlock (d n) (s n))

end

end STW22
end GroupApproximation
