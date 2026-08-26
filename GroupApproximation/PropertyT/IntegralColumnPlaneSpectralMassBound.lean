import GroupApproximation.PropertyT.IntegralColumnPlaneSpectralCoreBound
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.Data.Finsupp.Encodable

/-!
# Scalar spectral mass bound for the integral column plane

The unit-root displacement identities control the two outer strips of the
scalar torus.  Combining those bounds with the four-shear theorem gives the
exact mass estimate away from the trivial scalar character.
-/

namespace GroupApproximation
namespace IntegralColumnPlaneSpectralMassBound

open MeasureTheory Set WeakDual
open IntegralCharacterMass IntegralColumnPlaneSpectralMeasure
open IntegralColumnPlaneSpectralShear
open IntegralColumnPlaneSpectralTorus IntegralColumnPlaneSpectralCoreBound
open KassabovRankZeroTorusGeometry
open RepresentedRootPlaneSpectralMeasure

noncomputable section

universe u v

/-- A point at least one quarter of the way around the additive circle has
squared chordal displacement from `1` at least `2`. -/
theorem two_le_norm_toCircle_sub_one_sq_of_one_fourth_le_abs_centered
    (x : AddCircle (1 : ℝ))
    (hx : (1 / 4 : ℝ) ≤ |centeredRepresentative x|) :
    2 ≤ ‖(x.toCircle : ℂ) - 1‖ ^ 2 := by
  let r := centeredRepresentative x
  have hrange :=
    (AddCircle.measurableEquivIoc (1 : ℝ) (-(1 / 2 : ℝ)) x).property
  change -(1 / 2 : ℝ) < r ∧ r ≤ -(1 / 2 : ℝ) + 1 at hrange
  have habsle : |r| ≤ (1 / 2 : ℝ) := by
    rw [abs_le]
    constructor <;> linarith
  have hangleLower : Real.pi / 2 ≤ |2 * Real.pi * r| := by
    have htwoPi : 0 ≤ 2 * Real.pi :=
      mul_nonneg (by norm_num) Real.pi_pos.le
    rw [abs_mul, abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2),
      abs_of_pos Real.pi_pos]
    have hx' : (1 / 4 : ℝ) ≤ |r| := hx
    have hmul := mul_le_mul_of_nonneg_left hx' htwoPi
    nlinarith
  have hangleUpper :
      |2 * Real.pi * r| ≤ Real.pi + Real.pi / 2 := by
    have htwoPi : 0 ≤ 2 * Real.pi :=
      mul_nonneg (by norm_num) Real.pi_pos.le
    rw [abs_mul, abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2),
      abs_of_pos Real.pi_pos]
    have hmul := mul_le_mul_of_nonneg_left habsle htwoPi
    nlinarith [Real.pi_pos]
  have hcos : Real.cos (2 * Real.pi * r) ≤ 0 := by
    rw [← Real.cos_abs]
    exact Real.cos_nonpos_of_pi_div_two_le_of_le hangleLower hangleUpper
  have hre : ((x.toCircle : Circle) : ℂ).re =
      Real.cos (2 * Real.pi * r) := by
    rw [← coe_centeredRepresentative x]
    change ((AddCircle.toCircle (r : AddCircle (1 : ℝ)) : Circle) : ℂ).re = _
    rw [AddCircle.toCircle_apply_mk, div_one, Circle.coe_exp]
    exact Complex.exp_ofReal_mul_I_re _
  rw [Complex.norm_sub_one_sq_eq_of_norm_eq_one (by
    exact x.toCircle.norm_coe), hre]
  linarith

private def firstChordSq (p : Torus) : ℝ :=
  ‖(p.1.toCircle : ℂ) - 1‖ ^ 2

private def secondChordSq (p : Torus) : ℝ :=
  ‖(p.2.toCircle : ℂ) - 1‖ ^ 2

private theorem continuous_firstChordSq : Continuous firstChordSq := by
  unfold firstChordSq
  fun_prop

private theorem continuous_secondChordSq : Continuous secondChordSq := by
  unfold secondChordSq
  fun_prop

private theorem two_mul_measureReal_verticalOuter_le_integral_firstChordSq
    (mu : Measure Torus) [IsFiniteMeasure mu] :
    2 * mu.real verticalOuter ≤ ∫ p, firstChordSq p ∂mu := by
  have hconst : Integrable (fun _ : Torus ↦ (2 : ℝ)) mu := integrable_const 2
  have hleft := hconst.indicator measurableSet_verticalOuter
  have hright : Integrable firstChordSq mu :=
    continuous_firstChordSq.integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace firstChordSq)
  have hmono :
      ∫ p, verticalOuter.indicator (fun _ ↦ (2 : ℝ)) p ∂mu ≤
        ∫ p, firstChordSq p ∂mu := by
    apply integral_mono hleft hright
    intro p
    by_cases hp : p ∈ verticalOuter
    · rw [indicator_of_mem hp]
      exact two_le_norm_toCircle_sub_one_sq_of_one_fourth_le_abs_centered
        p.1 hp
    · rw [Set.indicator_of_notMem hp]
      exact sq_nonneg _
  rw [integral_indicator_const (2 : ℝ) measurableSet_verticalOuter] at hmono
  simpa [smul_eq_mul, mul_comm] using hmono

private theorem two_mul_measureReal_horizontalOuter_le_integral_secondChordSq
    (mu : Measure Torus) [IsFiniteMeasure mu] :
    2 * mu.real horizontalOuter ≤ ∫ p, secondChordSq p ∂mu := by
  have hconst : Integrable (fun _ : Torus ↦ (2 : ℝ)) mu := integrable_const 2
  have hleft := hconst.indicator measurableSet_horizontalOuter
  have hright : Integrable secondChordSq mu :=
    continuous_secondChordSq.integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace secondChordSq)
  have hmono :
      ∫ p, horizontalOuter.indicator (fun _ ↦ (2 : ℝ)) p ∂mu ≤
        ∫ p, secondChordSq p ∂mu := by
    apply integral_mono hleft hright
    intro p
    by_cases hp : p ∈ horizontalOuter
    · rw [indicator_of_mem hp]
      exact two_le_norm_toCircle_sub_one_sq_of_one_fourth_le_abs_centered
        p.2 hp
    · rw [Set.indicator_of_notMem hp]
      exact sq_nonneg _
  rw [integral_indicator_const (2 : ℝ) measurableSet_horizontalOuter] at hmono
  simpa [smul_eq_mul, mul_comm] using hmono

variable {E : Type v} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [CompleteSpace E]
variable {X : Type u} [Fintype X]

private abbrev R := FreeAlgebra ℤ X
private abbrev P
    (rho : elementaryGroup (Fin 3) (R (X := X)) →* (E ≃ₗᵢ[ℝ] E)) :=
  representedColumnPlane rho

private abbrev Spectrum
    (rho : elementaryGroup (Fin 3) (R (X := X)) →* (E ≃ₗᵢ[ℝ] E)) :=
  characterSpace ℂ (P rho).algebra

noncomputable local instance representedColumnPlaneSpectrumMeasurableSpace
    (rho : elementaryGroup (Fin 3) (R (X := X)) →* (E ≃ₗᵢ[ℝ] E)) :
    MeasurableSpace (Spectrum rho) :=
  borel _

local instance representedColumnPlaneSpectrumBorelSpace
    (rho : elementaryGroup (Fin 3) (R (X := X)) →* (E ≃ₗᵢ[ℝ] E)) :
    BorelSpace (Spectrum rho) :=
  ⟨rfl⟩

omit [Fintype X] in
/-- The integral free algebra on a countable alphabet is countable.  We
expose this locally so countable unions over all coefficient coordinates can
be used without adding a hypothesis to the finite-alphabet theorems. -/
noncomputable local instance integralFreeAlgebraCountable [Countable X] :
    Countable (R (X := X)) := by
  letI : Countable (FreeMonoid X) :=
    Countable.of_equiv (List X) (FreeMonoid.ofList (α := X))
  letI : Countable (MonoidAlgebra ℤ (FreeMonoid X)) :=
    Countable.of_equiv ((FreeMonoid X) →₀ ℤ)
      (MonoidAlgebra.coeffEquiv (R := ℤ) (M := FreeMonoid X)).symm
  exact Countable.of_equiv (MonoidAlgebra ℤ (FreeMonoid X))
    (FreeAlgebra.equivMonoidAlgebraFreeMonoid
      (R := ℤ) (X := X)).symm.toEquiv

noncomputable local instance scalarTorusMeasureIsFinite
    (rho : elementaryGroup (Fin 3) (R (X := X)) →* (E ≃ₗᵢ[ℝ] E))
    (z : E) (hz : ‖z‖ = 1) :
    IsFiniteMeasure (scalarTorusMeasure rho z hz) := by
  unfold scalarTorusMeasure
  exact Measure.isFiniteMeasure_map _ _

/-! ### The scalar zero fiber versus the full plane support -/

omit [Fintype X] in
/-- A scalar torus coordinate is zero exactly when the character is trivial
on the two unit-coefficient column roots. -/
theorem scalarTorusCoordinate_eq_zero_iff
    (rho : elementaryGroup (Fin 3) (R (X := X)) →* (E ≃ₗᵢ[ℝ] E))
    (chi : Spectrum rho) :
    scalarTorusCoordinate rho chi = (0, 0) ↔
      chi ((P rho).coordinate (0, 1)) = 1 ∧
        chi ((P rho).coordinate (1, 1)) = 1 := by
  constructor
  · intro hzero
    have hzero0 := congrArg Prod.fst hzero
    have hzero1 := congrArg Prod.snd hzero
    change coordinateAngle rho (0, 1) chi = 0 at hzero0
    change coordinateAngle rho (1, 1) chi = 0 at hzero1
    have hcircle0 := congrArg
      (fun a : AddCircle (1 : ℝ) ↦ (a.toCircle : ℂ)) hzero0
    have hcircle1 := congrArg
      (fun a : AddCircle (1 : ℝ) ↦ (a.toCircle : ℂ)) hzero1
    rw [coordinateAngle_toCircle, coordinateCircle_coe,
      AddCircle.toCircle_zero] at hcircle0 hcircle1
    exact ⟨hcircle0, hcircle1⟩
  · rintro ⟨hzero0, hzero1⟩
    apply Prod.ext
    · change coordinateAngle rho (0, 1) chi = 0
      apply AddCircle.injective_toCircle (by norm_num)
      rw [coordinateAngle_toCircle, AddCircle.toCircle_zero]
      apply Circle.ext
      exact hzero0
    · change coordinateAngle rho (1, 1) chi = 0
      apply AddCircle.injective_toCircle (by norm_num)
      rw [coordinateAngle_toCircle, AddCircle.toCircle_zero]
      apply Circle.ext
      exact hzero1

/-- Characters detected as nontrivial by the two unit-coefficient column
roots. -/
def unitRootNontrivialSet
    (rho : elementaryGroup (Fin 3) (R (X := X)) →* (E ≃ₗᵢ[ℝ] E)) :
    Set (Spectrum rho) :=
  {chi | chi ((P rho).coordinate (0, 1)) ≠ 1 ∨
    chi ((P rho).coordinate (1, 1)) ≠ 1}

/-- Characters nontrivial on at least one coefficient in the full represented
column plane. -/
def fullPlaneNontrivialSet
    (rho : elementaryGroup (Fin 3) (R (X := X)) →* (E ≃ₗᵢ[ℝ] E)) :
    Set (Spectrum rho) :=
  {chi | ∃ q : Fin 2 × R (X := X), chi ((P rho).coordinate q) ≠ 1}

omit [Fintype X] in
/-- One arbitrary coefficient coordinate is zero precisely when the
corresponding character evaluation is trivial. -/
theorem coordinateAngle_eq_zero_iff
    (rho : elementaryGroup (Fin 3) (R (X := X)) →* (E ≃ₗᵢ[ℝ] E))
    (q : Fin 2 × R (X := X)) (chi : Spectrum rho) :
    coordinateAngle rho q chi = 0 ↔
      chi ((P rho).coordinate q) = 1 := by
  constructor
  · intro hzero
    have hcircle := congrArg
      (fun a : AddCircle (1 : ℝ) ↦ (a.toCircle : ℂ)) hzero
    rw [coordinateAngle_toCircle, coordinateCircle_coe,
      AddCircle.toCircle_zero] at hcircle
    exact hcircle
  · intro hzero
    apply AddCircle.injective_toCircle (by norm_num)
    rw [coordinateAngle_toCircle, AddCircle.toCircle_zero]
    apply Circle.ext
    exact hzero

/-- The part of the character spectrum detected by a finite family of
coefficient coordinates. -/
def finitePlaneNontrivialSet
    (rho : elementaryGroup (Fin 3) (R (X := X)) →* (E ≃ₗᵢ[ℝ] E))
    (s : Finset (Fin 2 × R (X := X))) : Set (Spectrum rho) :=
  {chi | ∃ q ∈ s, chi ((P rho).coordinate q) ≠ 1}

/-- Enlarging a finite coefficient family by the coordinates needed to read
the action of one upper shear.  Including the extra coordinate also for the
fixed first-root coordinates keeps the construction uniform and harmless. -/
noncomputable def upperFiniteCoefficientClosure
    (r : R (X := X)) (s : Finset (Fin 2 × R (X := X))) :
    Finset (Fin 2 × R (X := X)) := by
  classical
  exact s ∪ s.image (fun q ↦ ((0 : Fin 2), r * q.2))

/-- Enlarging a finite coefficient family by the coordinates needed to read
the action of one lower shear. -/
noncomputable def lowerFiniteCoefficientClosure
    (r : R (X := X)) (s : Finset (Fin 2 × R (X := X))) :
    Finset (Fin 2 × R (X := X)) := by
  classical
  exact s ∪ s.image (fun q ↦ ((1 : Fin 2), r * q.2))

/-- One simultaneous finite enlargement for every unit/free-generator shear
in the integral control set.  Its size depends on the fixed alphabet but not
on a polynomial degree stage. -/
noncomputable def integralFiniteCoefficientClosure
    (s : Finset (Fin 2 × R (X := X))) :
    Finset (Fin 2 × R (X := X)) := by
  classical
  exact s ∪ (Finset.univ : Finset (Option X)).biUnion (fun q ↦
    s.image (fun p ↦ ((0 : Fin 2), integralControlCoefficient X q * p.2)) ∪
      s.image (fun p ↦ ((1 : Fin 2), integralControlCoefficient X q * p.2)))

/-- The finite family of the two root coordinates whose coefficients are
word monomials of degree at most `n`. -/
noncomputable def wordCoordinateSet (n : ℕ) :
    Finset (Fin 2 × R (X := X)) := by
  classical
  exact (Finset.univ : Finset (Fin 2)).biUnion fun b ↦
    (FreeAlgebraDegree.freeWordsLE X n).image fun w ↦
      (b, FreeAlgebraDegree.wordMonomial X ℤ w)

/-- The degree-bounded word coordinates in one of the two root subgroups. -/
noncomputable def rootWordCoordinateSet (b : Fin 2) (n : ℕ) :
    Finset (Fin 2 × R (X := X)) := by
  classical
  exact (FreeAlgebraDegree.freeWordsLE X n).image fun w ↦
    (b, FreeAlgebraDegree.wordMonomial X ℤ w)

theorem mem_rootWordCoordinateSet_iff
    (b c : Fin 2) (a : R (X := X)) (n : ℕ) :
    (c, a) ∈ rootWordCoordinateSet (X := X) b n ↔
      c = b ∧ ∃ w : FreeMonoid X,
        FreeAlgebraDegree.freeWordLength X w ≤ n ∧
        FreeAlgebraDegree.wordMonomial X ℤ w = a := by
  classical
  constructor
  · intro h
    rw [rootWordCoordinateSet] at h
    obtain ⟨w, hw, heq⟩ := Finset.mem_image.mp h
    exact ⟨(congrArg Prod.fst heq).symm, w,
      (FreeAlgebraDegree.mem_freeWordsLE X w n).mp hw,
      congrArg Prod.snd heq⟩
  · rintro ⟨rfl, w, hw, ha⟩
    rw [rootWordCoordinateSet]
    exact Finset.mem_image.mpr
      ⟨w, (FreeAlgebraDegree.mem_freeWordsLE X w n).mpr hw,
        Prod.ext rfl ha⟩

theorem rootWordCoordinateSet_mono (b : Fin 2) {m n : ℕ} (hmn : m ≤ n) :
    rootWordCoordinateSet (X := X) b m ⊆
      rootWordCoordinateSet (X := X) b n := by
  rintro ⟨c, a⟩ h
  obtain ⟨hcb, w, hw, ha⟩ :=
    (mem_rootWordCoordinateSet_iff b c a m).mp h
  exact (mem_rootWordCoordinateSet_iff b c a n).mpr
    ⟨hcb, w, hw.trans hmn, ha⟩

theorem mem_wordCoordinateSet_iff (b : Fin 2) (a : R (X := X)) (n : ℕ) :
    (b, a) ∈ wordCoordinateSet (X := X) n ↔
      ∃ w : FreeMonoid X, FreeAlgebraDegree.freeWordLength X w ≤ n ∧
        FreeAlgebraDegree.wordMonomial X ℤ w = a := by
  classical
  constructor
  · intro h
    rw [wordCoordinateSet] at h
    obtain ⟨c, _, hc⟩ := Finset.mem_biUnion.mp h
    obtain ⟨w, hw, heq⟩ := Finset.mem_image.mp hc
    refine ⟨w, (FreeAlgebraDegree.mem_freeWordsLE X w n).mp hw, ?_⟩
    exact congrArg Prod.snd heq
  · rintro ⟨w, hw, ha⟩
    rw [wordCoordinateSet]
    apply Finset.mem_biUnion.mpr
    refine ⟨b, Finset.mem_univ b, ?_⟩
    apply Finset.mem_image.mpr
    refine ⟨w, (FreeAlgebraDegree.mem_freeWordsLE X w n).mpr hw, ?_⟩
    exact Prod.ext rfl ha

theorem wordCoordinateSet_mono {m n : ℕ} (hmn : m ≤ n) :
    wordCoordinateSet (X := X) m ⊆ wordCoordinateSet (X := X) n := by
  rintro ⟨b, a⟩ h
  obtain ⟨w, hw, ha⟩ := (mem_wordCoordinateSet_iff b a m).mp h
  exact (mem_wordCoordinateSet_iff b a n).mpr
    ⟨w, hw.trans hmn, ha⟩

/-- Left multiplication of a word monomial by any coefficient occurring in
the integral control set is again a word monomial, with degree increased by
at most one. -/
theorem exists_controlCoefficient_mul_wordMonomial
    (q : Option X) {w : FreeMonoid X} {n : ℕ}
    (hw : FreeAlgebraDegree.freeWordLength X w ≤ n) :
    ∃ v : FreeMonoid X,
      FreeAlgebraDegree.freeWordLength X v ≤ n + 1 ∧
      FreeAlgebraDegree.wordMonomial X ℤ v =
        integralControlCoefficient X q *
          FreeAlgebraDegree.wordMonomial X ℤ w := by
  cases q with
  | none =>
      refine ⟨w, hw.trans (Nat.le_succ n), ?_⟩
      simp [integralControlCoefficient]
  | some x =>
      refine ⟨FreeMonoid.of x * w, ?_, ?_⟩
      · rw [FreeAlgebraDegree.freeWordLength_mul,
          FreeAlgebraDegree.freeWordLength_of]
        omega
      · calc
          FreeAlgebraDegree.wordMonomial X ℤ (FreeMonoid.of x * w) =
              FreeAlgebraDegree.wordMonomial X ℤ (FreeMonoid.of x) *
                FreeAlgebraDegree.wordMonomial X ℤ w :=
            (FreeAlgebraDegree.wordMonomial_mul X ℤ _ _).symm
          _ = FreeAlgebra.ι ℤ x *
                FreeAlgebraDegree.wordMonomial X ℤ w := by
            rw [FreeAlgebraDegree.wordMonomial_of]
          _ = integralControlCoefficient X (some x) *
                FreeAlgebraDegree.wordMonomial X ℤ w := rfl

/-- One simultaneous round of every controlled upper and lower shear sends
degree-`n` word-coordinate dependencies into the degree-`n+1` family. -/
theorem integralFiniteCoefficientClosure_wordCoordinateSet_subset (n : ℕ) :
    integralFiniteCoefficientClosure (wordCoordinateSet (X := X) n) ⊆
      wordCoordinateSet (X := X) (n + 1) := by
  classical
  intro p hp
  rw [integralFiniteCoefficientClosure, Finset.mem_union] at hp
  rcases hp with hp | hp
  · exact wordCoordinateSet_mono (Nat.le_succ n) hp
  · obtain ⟨q, _, hq⟩ := Finset.mem_biUnion.mp hp
    rcases Finset.mem_union.mp hq with hq | hq
    · obtain ⟨⟨b, a⟩, ha, rfl⟩ := Finset.mem_image.mp hq
      obtain ⟨w, hw, hwa⟩ := (mem_wordCoordinateSet_iff b a n).mp ha
      obtain ⟨v, hv, hvcoeff⟩ :=
        exists_controlCoefficient_mul_wordMonomial q hw
      apply (mem_wordCoordinateSet_iff 0
        (integralControlCoefficient X q * a) (n + 1)).mpr
      exact ⟨v, hv, hvcoeff.trans (congrArg
        (fun c : R (X := X) ↦ integralControlCoefficient X q * c) hwa)⟩
    · obtain ⟨⟨b, a⟩, ha, rfl⟩ := Finset.mem_image.mp hq
      obtain ⟨w, hw, hwa⟩ := (mem_wordCoordinateSet_iff b a n).mp ha
      obtain ⟨v, hv, hvcoeff⟩ :=
        exists_controlCoefficient_mul_wordMonomial q hw
      apply (mem_wordCoordinateSet_iff 1
        (integralControlCoefficient X q * a) (n + 1)).mpr
      exact ⟨v, hv, hvcoeff.trans (congrArg
        (fun c : R (X := X) ↦ integralControlCoefficient X q * c) hwa)⟩

theorem upperFiniteCoefficientClosure_subset_integral
    (q : Option X) (s : Finset (Fin 2 × R (X := X))) :
    upperFiniteCoefficientClosure (integralControlCoefficient X q) s ⊆
      integralFiniteCoefficientClosure s := by
  classical
  intro p hp
  rw [upperFiniteCoefficientClosure, Finset.mem_union] at hp
  rw [integralFiniteCoefficientClosure, Finset.mem_union]
  rcases hp with hp | hp
  · exact Or.inl hp
  · right
    apply Finset.mem_biUnion.mpr
    refine ⟨q, Finset.mem_univ q, ?_⟩
    exact Finset.mem_union.mpr (Or.inl hp)

theorem lowerFiniteCoefficientClosure_subset_integral
    (q : Option X) (s : Finset (Fin 2 × R (X := X))) :
    lowerFiniteCoefficientClosure (integralControlCoefficient X q) s ⊆
      integralFiniteCoefficientClosure s := by
  classical
  intro p hp
  rw [lowerFiniteCoefficientClosure, Finset.mem_union] at hp
  rw [integralFiniteCoefficientClosure, Finset.mem_union]
  rcases hp with hp | hp
  · exact Or.inl hp
  · right
    apply Finset.mem_biUnion.mpr
    refine ⟨q, Finset.mem_univ q, ?_⟩
    exact Finset.mem_union.mpr (Or.inr hp)

/-- One round of all controlled shears enlarges a finite coordinate family by
at most a factor depending only on the fixed alphabet, never on the degree
of the coefficients already present. -/
theorem card_integralFiniteCoefficientClosure_le
    (s : Finset (Fin 2 × R (X := X))) :
    (integralFiniteCoefficientClosure s).card ≤
      (2 * Fintype.card (Option X) + 1) * s.card := by
  classical
  let f : Option X → Finset (Fin 2 × R (X := X)) := fun q ↦
    s.image (fun p ↦ ((0 : Fin 2), integralControlCoefficient X q * p.2)) ∪
      s.image (fun p ↦ ((1 : Fin 2), integralControlCoefficient X q * p.2))
  have hf : ∀ q, (f q).card ≤ 2 * s.card := by
    intro q
    calc
      (f q).card ≤
          (s.image (fun p ↦
            ((0 : Fin 2), integralControlCoefficient X q * p.2))).card +
          (s.image (fun p ↦
            ((1 : Fin 2), integralControlCoefficient X q * p.2))).card :=
        Finset.card_union_le _ _
      _ ≤ s.card + s.card :=
        Nat.add_le_add Finset.card_image_le Finset.card_image_le
      _ = 2 * s.card := by omega
  rw [integralFiniteCoefficientClosure]
  change (s ∪ (Finset.univ : Finset (Option X)).biUnion f).card ≤ _
  calc
    (s ∪ (Finset.univ : Finset (Option X)).biUnion f).card ≤
        s.card + ((Finset.univ : Finset (Option X)).biUnion f).card :=
      Finset.card_union_le _ _
    _ ≤ s.card + ∑ q ∈ (Finset.univ : Finset (Option X)), (f q).card :=
      Nat.add_le_add_left Finset.card_biUnion_le s.card
    _ ≤ s.card + ∑ _q ∈ (Finset.univ : Finset (Option X)),
          2 * s.card :=
      Nat.add_le_add_left (Finset.sum_le_sum fun q _ ↦ hf q) s.card
    _ = (2 * Fintype.card (Option X) + 1) * s.card := by
      simp
      ring

omit [Fintype X] in
/-- If an upper shear makes a character visible on a finite coordinate
family, the original character is visible on the corresponding finite
coefficient closure. -/
theorem finitePlaneNontrivialSet_of_characterAction_upper_mem
    (rho : elementaryGroup (Fin 3) (R (X := X)) →* (E ≃ₗᵢ[ℝ] E))
    (r : R (X := X)) (s : Finset (Fin 2 × R (X := X)))
    (chi : Spectrum rho)
    (hchi : CommutativeCStarCovariance.characterAction (P rho).algebra
        ((P rho).rho (upperShear r))
        (upperShear_forward rho r) (upperShear_backward rho r) chi ∈
      finitePlaneNontrivialSet rho s) :
    chi ∈ finitePlaneNontrivialSet rho
      (upperFiniteCoefficientClosure r s) := by
  classical
  rcases hchi with ⟨⟨b, a⟩, hmem, hnontrivial⟩
  fin_cases b
  · have hangle : coordinateAngle rho (0, a)
        (CommutativeCStarCovariance.characterAction (P rho).algebra
          ((P rho).rho (upperShear r))
          (upperShear_forward rho r) (upperShear_backward rho r) chi) ≠ 0 :=
      fun hzero ↦ hnontrivial
        ((coordinateAngle_eq_zero_iff rho (0, a) _).mp hzero)
    rw [coordinateAngle_characterAction_upper_zero] at hangle
    refine ⟨(0, a), ?_, ?_⟩
    · exact Finset.mem_union.mpr (Or.inl hmem)
    · exact fun hzero ↦ hangle
        ((coordinateAngle_eq_zero_iff rho (0, a) chi).mpr hzero)
  · have hangle : coordinateAngle rho (1, a)
        (CommutativeCStarCovariance.characterAction (P rho).algebra
          ((P rho).rho (upperShear r))
          (upperShear_forward rho r) (upperShear_backward rho r) chi) ≠ 0 :=
      fun hzero ↦ hnontrivial
        ((coordinateAngle_eq_zero_iff rho (1, a) _).mp hzero)
    rw [coordinateAngle_characterAction_upper_one] at hangle
    have hparts : coordinateAngle rho (0, r * a) chi ≠ 0 ∨
        coordinateAngle rho (1, a) chi ≠ 0 := by
      by_contra hboth
      push_neg at hboth
      exact hangle (by rw [hboth.1, hboth.2, zero_add])
    rcases hparts with hleft | hright
    · refine ⟨(0, r * a), ?_, ?_⟩
      · apply Finset.mem_union.mpr
        apply Or.inr
        exact Finset.mem_image.mpr ⟨(1, a), hmem, rfl⟩
      · exact fun hzero ↦ hleft
          ((coordinateAngle_eq_zero_iff rho (0, r * a) chi).mpr hzero)
    · refine ⟨(1, a), ?_, ?_⟩
      · exact Finset.mem_union.mpr (Or.inl hmem)
      · exact fun hzero ↦ hright
          ((coordinateAngle_eq_zero_iff rho (1, a) chi).mpr hzero)

omit [Fintype X] in
/-- If a lower shear makes a character visible on a finite coordinate
family, the original character is visible on the corresponding finite
coefficient closure. -/
theorem finitePlaneNontrivialSet_of_characterAction_lower_mem
    (rho : elementaryGroup (Fin 3) (R (X := X)) →* (E ≃ₗᵢ[ℝ] E))
    (r : R (X := X)) (s : Finset (Fin 2 × R (X := X)))
    (chi : Spectrum rho)
    (hchi : CommutativeCStarCovariance.characterAction (P rho).algebra
        ((P rho).rho (lowerShear r))
        (lowerShear_forward rho r) (lowerShear_backward rho r) chi ∈
      finitePlaneNontrivialSet rho s) :
    chi ∈ finitePlaneNontrivialSet rho
      (lowerFiniteCoefficientClosure r s) := by
  classical
  rcases hchi with ⟨⟨b, a⟩, hmem, hnontrivial⟩
  fin_cases b
  · have hangle : coordinateAngle rho (0, a)
        (CommutativeCStarCovariance.characterAction (P rho).algebra
          ((P rho).rho (lowerShear r))
          (lowerShear_forward rho r) (lowerShear_backward rho r) chi) ≠ 0 :=
      fun hzero ↦ hnontrivial
        ((coordinateAngle_eq_zero_iff rho (0, a) _).mp hzero)
    rw [coordinateAngle_characterAction_lower_zero] at hangle
    have hparts : coordinateAngle rho (1, r * a) chi ≠ 0 ∨
        coordinateAngle rho (0, a) chi ≠ 0 := by
      by_contra hboth
      push_neg at hboth
      exact hangle (by rw [hboth.1, hboth.2, zero_add])
    rcases hparts with hleft | hright
    · refine ⟨(1, r * a), ?_, ?_⟩
      · apply Finset.mem_union.mpr
        apply Or.inr
        exact Finset.mem_image.mpr ⟨(0, a), hmem, rfl⟩
      · exact fun hzero ↦ hleft
          ((coordinateAngle_eq_zero_iff rho (1, r * a) chi).mpr hzero)
    · refine ⟨(0, a), ?_, ?_⟩
      · exact Finset.mem_union.mpr (Or.inl hmem)
      · exact fun hzero ↦ hright
          ((coordinateAngle_eq_zero_iff rho (0, a) chi).mpr hzero)
  · have hangle : coordinateAngle rho (1, a)
        (CommutativeCStarCovariance.characterAction (P rho).algebra
          ((P rho).rho (lowerShear r))
          (lowerShear_forward rho r) (lowerShear_backward rho r) chi) ≠ 0 :=
      fun hzero ↦ hnontrivial
        ((coordinateAngle_eq_zero_iff rho (1, a) _).mp hzero)
    rw [coordinateAngle_characterAction_lower_one] at hangle
    refine ⟨(1, a), ?_, ?_⟩
    · exact Finset.mem_union.mpr (Or.inl hmem)
    · exact fun hzero ↦ hangle
        ((coordinateAngle_eq_zero_iff rho (1, a) chi).mpr hzero)

/-- A single finite enlargement works for the pullback of a finite visible
set under every controlled upper shear. -/
theorem finitePlaneNontrivialSet_of_controlled_characterAction_upper_mem
    (rho : elementaryGroup (Fin 3) (R (X := X)) →* (E ≃ₗᵢ[ℝ] E))
    (q : Option X) (s : Finset (Fin 2 × R (X := X)))
    (chi : Spectrum rho)
    (hchi : CommutativeCStarCovariance.characterAction (P rho).algebra
        ((P rho).rho (upperShear (integralControlCoefficient X q)))
        (upperShear_forward rho _) (upperShear_backward rho _) chi ∈
      finitePlaneNontrivialSet rho s) :
    chi ∈ finitePlaneNontrivialSet rho
      (integralFiniteCoefficientClosure s) := by
  obtain ⟨p, hp, hnontrivial⟩ :=
    finitePlaneNontrivialSet_of_characterAction_upper_mem rho
      (integralControlCoefficient X q) s chi hchi
  exact ⟨p, upperFiniteCoefficientClosure_subset_integral q s hp,
    hnontrivial⟩

/-- A single finite enlargement works for the pullback of a finite visible
set under every controlled lower shear. -/
theorem finitePlaneNontrivialSet_of_controlled_characterAction_lower_mem
    (rho : elementaryGroup (Fin 3) (R (X := X)) →* (E ≃ₗᵢ[ℝ] E))
    (q : Option X) (s : Finset (Fin 2 × R (X := X)))
    (chi : Spectrum rho)
    (hchi : CommutativeCStarCovariance.characterAction (P rho).algebra
        ((P rho).rho (lowerShear (integralControlCoefficient X q)))
        (lowerShear_forward rho _) (lowerShear_backward rho _) chi ∈
      finitePlaneNontrivialSet rho s) :
    chi ∈ finitePlaneNontrivialSet rho
      (integralFiniteCoefficientClosure s) := by
  obtain ⟨p, hp, hnontrivial⟩ :=
    finitePlaneNontrivialSet_of_characterAction_lower_mem rho
      (integralControlCoefficient X q) s chi hchi
  exact ⟨p, lowerFiniteCoefficientClosure_subset_integral q s hp,
    hnontrivial⟩

/-- Pulling the degree-`n` visible set back through a controlled upper shear
lands in the degree-`n+1` visible set. -/
theorem wordCoordinateNontrivial_of_controlled_characterAction_upper_mem
    (rho : elementaryGroup (Fin 3) (R (X := X)) →* (E ≃ₗᵢ[ℝ] E))
    (q : Option X) (n : ℕ) (chi : Spectrum rho)
    (hchi : CommutativeCStarCovariance.characterAction (P rho).algebra
        ((P rho).rho (upperShear (integralControlCoefficient X q)))
        (upperShear_forward rho _) (upperShear_backward rho _) chi ∈
      finitePlaneNontrivialSet rho (wordCoordinateSet (X := X) n)) :
    chi ∈ finitePlaneNontrivialSet rho
      (wordCoordinateSet (X := X) (n + 1)) := by
  obtain ⟨p, hp, hnontrivial⟩ :=
    finitePlaneNontrivialSet_of_controlled_characterAction_upper_mem
      rho q (wordCoordinateSet (X := X) n) chi hchi
  exact ⟨p, integralFiniteCoefficientClosure_wordCoordinateSet_subset n hp,
    hnontrivial⟩

/-- Pulling the degree-`n` visible set back through a controlled lower shear
lands in the degree-`n+1` visible set. -/
theorem wordCoordinateNontrivial_of_controlled_characterAction_lower_mem
    (rho : elementaryGroup (Fin 3) (R (X := X)) →* (E ≃ₗᵢ[ℝ] E))
    (q : Option X) (n : ℕ) (chi : Spectrum rho)
    (hchi : CommutativeCStarCovariance.characterAction (P rho).algebra
        ((P rho).rho (lowerShear (integralControlCoefficient X q)))
        (lowerShear_forward rho _) (lowerShear_backward rho _) chi ∈
      finitePlaneNontrivialSet rho (wordCoordinateSet (X := X) n)) :
    chi ∈ finitePlaneNontrivialSet rho
      (wordCoordinateSet (X := X) (n + 1)) := by
  obtain ⟨p, hp, hnontrivial⟩ :=
    finitePlaneNontrivialSet_of_controlled_characterAction_lower_mem
      rho q (wordCoordinateSet (X := X) n) chi hchi
  exact ⟨p, integralFiniteCoefficientClosure_wordCoordinateSet_subset n hp,
    hnontrivial⟩

omit [Fintype X] in
theorem finitePlaneNontrivialSet_mono
    (rho : elementaryGroup (Fin 3) (R (X := X)) →* (E ≃ₗᵢ[ℝ] E))
    {s t : Finset (Fin 2 × R (X := X))} (hst : s ⊆ t) :
    finitePlaneNontrivialSet rho s ⊆ finitePlaneNontrivialSet rho t := by
  rintro chi ⟨q, hqs, hq⟩
  exact ⟨q, hst hqs, hq⟩

omit [Fintype X] in
theorem finitePlaneNontrivialSet_subset_fullPlaneNontrivialSet
    (rho : elementaryGroup (Fin 3) (R (X := X)) →* (E ≃ₗᵢ[ℝ] E))
    (s : Finset (Fin 2 × R (X := X))) :
    finitePlaneNontrivialSet rho s ⊆ fullPlaneNontrivialSet rho := by
  rintro chi ⟨q, _, hq⟩
  exact ⟨q, hq⟩

omit [Fintype X] in
theorem measurableSet_finitePlaneNontrivialSet
    (rho : elementaryGroup (Fin 3) (R (X := X)) →* (E ≃ₗᵢ[ℝ] E))
    (s : Finset (Fin 2 × R (X := X))) :
    MeasurableSet (finitePlaneNontrivialSet rho s) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
      simp [finitePlaneNontrivialSet]
  | @insert q s hqs ih =>
      have hsingle : MeasurableSet
          {chi : Spectrum rho | chi ((P rho).coordinate q) ≠ 1} := by
        have hset :
            {chi : Spectrum rho | chi ((P rho).coordinate q) ≠ 1} =
              coordinateAngle rho q ⁻¹' ({0}ᶜ : Set (AddCircle (1 : ℝ))) := by
          ext chi
          simp only [Set.mem_setOf_eq, Set.mem_preimage, Set.mem_compl_iff,
            Set.mem_singleton_iff]
          exact (not_congr (coordinateAngle_eq_zero_iff rho q chi)).symm
        rw [hset]
        exact (measurableSet_singleton (0 : AddCircle (1 : ℝ))).compl.preimage
          (continuous_coordinateAngle rho q).measurable
      have hunion : finitePlaneNontrivialSet rho (insert q s) =
          {chi : Spectrum rho | chi ((P rho).coordinate q) ≠ 1} ∪
            finitePlaneNontrivialSet rho s := by
        ext chi
        simp [finitePlaneNontrivialSet]
      rw [hunion]
      exact hsingle.union ih

/-! ### Least detected word degree -/

/-- Characters detected on a word monomial of degree at most `n` in one
fixed root subgroup. -/
def rootWordVisibleSet
    (rho : elementaryGroup (Fin 3) (R (X := X)) →* (E ≃ₗᵢ[ℝ] E))
    (b : Fin 2) (n : ℕ) : Set (Spectrum rho) :=
  finitePlaneNontrivialSet rho (rootWordCoordinateSet (X := X) b n)

theorem rootWordVisibleSet_mono
    (rho : elementaryGroup (Fin 3) (R (X := X)) →* (E ≃ₗᵢ[ℝ] E))
    (b : Fin 2) {m n : ℕ} (hmn : m ≤ n) :
    rootWordVisibleSet rho b m ⊆ rootWordVisibleSet rho b n :=
  finitePlaneNontrivialSet_mono rho (rootWordCoordinateSet_mono b hmn)

theorem measurableSet_rootWordVisibleSet
    (rho : elementaryGroup (Fin 3) (R (X := X)) →* (E ≃ₗᵢ[ℝ] E))
    (b : Fin 2) (n : ℕ) :
    MeasurableSet (rootWordVisibleSet rho b n) :=
  measurableSet_finitePlaneNontrivialSet rho _

/-- The cumulative detection set strictly before degree `d`.  Monotonicity
of the degree filtration makes this just the preceding visible set. -/
def rootWordVisibleBefore
    (rho : elementaryGroup (Fin 3) (R (X := X)) →* (E ≃ₗᵢ[ℝ] E))
    (b : Fin 2) : ℕ → Set (Spectrum rho)
  | 0 => ∅
  | d + 1 => rootWordVisibleSet rho b d

theorem measurableSet_rootWordVisibleBefore
    (rho : elementaryGroup (Fin 3) (R (X := X)) →* (E ≃ₗᵢ[ℝ] E))
    (b : Fin 2) (d : ℕ) :
    MeasurableSet (rootWordVisibleBefore rho b d) := by
  cases d with
  | zero => exact MeasurableSet.empty
  | succ d => exact measurableSet_rootWordVisibleSet rho b d

/-- The Borel cell on which `d` is the least word degree detected in one
fixed root subgroup. -/
def leastRootWordDetectionSet
    (rho : elementaryGroup (Fin 3) (R (X := X)) →* (E ≃ₗᵢ[ℝ] E))
    (b : Fin 2) (d : ℕ) : Set (Spectrum rho) :=
  rootWordVisibleSet rho b d \ rootWordVisibleBefore rho b d

theorem measurableSet_leastRootWordDetectionSet
    (rho : elementaryGroup (Fin 3) (R (X := X)) →* (E ≃ₗᵢ[ℝ] E))
    (b : Fin 2) (d : ℕ) :
    MeasurableSet (leastRootWordDetectionSet rho b d) :=
  (measurableSet_rootWordVisibleSet rho b d).diff
    (measurableSet_rootWordVisibleBefore rho b d)

/-- Distinct least-degree cells for one root subgroup are disjoint. -/
theorem disjoint_leastRootWordDetectionSet
    (rho : elementaryGroup (Fin 3) (R (X := X)) →* (E ≃ₗᵢ[ℝ] E))
    (b : Fin 2) {d e : ℕ} (hde : d ≠ e) :
    Disjoint (leastRootWordDetectionSet rho b d)
      (leastRootWordDetectionSet rho b e) := by
  apply Set.disjoint_left.mpr
  intro chi hd he
  change chi ∈ rootWordVisibleSet rho b d ∧
      chi ∉ rootWordVisibleBefore rho b d at hd
  change chi ∈ rootWordVisibleSet rho b e ∧
      chi ∉ rootWordVisibleBefore rho b e at he
  rcases lt_or_gt_of_ne hde with hlt | hgt
  · cases e with
    | zero => omega
    | succ k =>
        apply he.2
        exact rootWordVisibleSet_mono rho b (by omega) hd.1
  · cases d with
    | zero => omega
    | succ k =>
        apply hd.2
        exact rootWordVisibleSet_mono rho b (by omega) he.1

/-- The least detected word degree up to stage `n`; `n+1` is the sentinel
when the character is trivial on the entire degree-`n` root family. -/
noncomputable def leastRootWordDegreeWithin
    (rho : elementaryGroup (Fin 3) (R (X := X)) →* (E ≃ₗᵢ[ℝ] E))
    (b : Fin 2) (n : ℕ) (chi : Spectrum rho) : ℕ := by
  classical
  exact if h : ∃ d, d ≤ n ∧ chi ∈ rootWordVisibleSet rho b d then
    Nat.find h
  else n + 1

theorem leastRootWordDegreeWithin_le
    (rho : elementaryGroup (Fin 3) (R (X := X)) →* (E ≃ₗᵢ[ℝ] E))
    (b : Fin 2) (n : ℕ) (chi : Spectrum rho)
    (hchi : chi ∈ rootWordVisibleSet rho b n) :
    leastRootWordDegreeWithin rho b n chi ≤ n := by
  classical
  let h : ∃ d, d ≤ n ∧ chi ∈ rootWordVisibleSet rho b d :=
    ⟨n, le_rfl, hchi⟩
  rw [leastRootWordDegreeWithin, dif_pos h]
  exact Nat.find_min' h ⟨n, le_rfl, hchi⟩

theorem leastRootWordDegreeWithin_mem
    (rho : elementaryGroup (Fin 3) (R (X := X)) →* (E ≃ₗᵢ[ℝ] E))
    (b : Fin 2) (n : ℕ) (chi : Spectrum rho)
    (hchi : chi ∈ rootWordVisibleSet rho b n) :
    chi ∈ rootWordVisibleSet rho b
      (leastRootWordDegreeWithin rho b n chi) := by
  classical
  let h : ∃ d, d ≤ n ∧ chi ∈ rootWordVisibleSet rho b d :=
    ⟨n, le_rfl, hchi⟩
  rw [leastRootWordDegreeWithin, dif_pos h]
  exact (Nat.find_spec h).2

theorem not_mem_rootWordVisibleSet_of_lt_leastRootWordDegreeWithin
    (rho : elementaryGroup (Fin 3) (R (X := X)) →* (E ≃ₗᵢ[ℝ] E))
    (b : Fin 2) (n : ℕ) (chi : Spectrum rho)
    (hchi : chi ∈ rootWordVisibleSet rho b n) {d : ℕ}
    (hd : d < leastRootWordDegreeWithin rho b n chi) :
    chi ∉ rootWordVisibleSet rho b d := by
  classical
  intro hdmem
  let h : ∃ e, e ≤ n ∧ chi ∈ rootWordVisibleSet rho b e :=
    ⟨n, le_rfl, hchi⟩
  have hfindle : Nat.find h ≤ n := Nat.find_min' h ⟨n, le_rfl, hchi⟩
  have hdle : d ≤ n := by
    rw [leastRootWordDegreeWithin, dif_pos h] at hd
    omega
  have hminimal := Nat.find_min' h ⟨d, hdle, hdmem⟩
  rw [leastRootWordDegreeWithin, dif_pos h] at hd
  omega

/-- A character visible by degree `n` belongs to the least-degree cell
selected by `leastRootWordDegreeWithin`. -/
theorem mem_leastRootWordDetectionSet_leastRootWordDegreeWithin
    (rho : elementaryGroup (Fin 3) (R (X := X)) →* (E ≃ₗᵢ[ℝ] E))
    (b : Fin 2) (n : ℕ) (chi : Spectrum rho)
    (hchi : chi ∈ rootWordVisibleSet rho b n) :
    chi ∈ leastRootWordDetectionSet rho b
      (leastRootWordDegreeWithin rho b n chi) := by
  refine ⟨leastRootWordDegreeWithin_mem rho b n chi hchi, ?_⟩
  generalize hdegree : leastRootWordDegreeWithin rho b n chi = d
  cases d with
  | zero => exact Set.not_mem_empty chi
  | succ k =>
      change chi ∉ rootWordVisibleSet rho b k
      apply not_mem_rootWordVisibleSet_of_lt_leastRootWordDegreeWithin
        rho b n chi hchi
      omega

/-- The least-degree cells through stage `n` are a disjoint exhaustion of
the degree-`n` visible set. -/
theorem iUnion_leastRootWordDetectionSet_range
    (rho : elementaryGroup (Fin 3) (R (X := X)) →* (E ≃ₗᵢ[ℝ] E))
    (b : Fin 2) (n : ℕ) :
    (⋃ d ∈ (Finset.range (n + 1) : Set ℕ),
      leastRootWordDetectionSet rho b d) = rootWordVisibleSet rho b n := by
  ext chi
  constructor
  · intro hchi
    obtain ⟨d, hd⟩ := Set.mem_iUnion.mp hchi
    obtain ⟨hdrange, hdcell⟩ := Set.mem_iUnion.mp hd
    have hdle : d ≤ n := by
      have := Finset.mem_range.mp (Finset.mem_coe.mp hdrange)
      omega
    exact rootWordVisibleSet_mono rho b hdle hdcell.1
  · intro hchi
    let d := leastRootWordDegreeWithin rho b n chi
    have hdle : d ≤ n := leastRootWordDegreeWithin_le rho b n chi hchi
    apply Set.mem_iUnion.mpr
    refine ⟨d, Set.mem_iUnion.mpr ⟨?_, ?_⟩⟩
    · exact Finset.mem_coe.mpr (Finset.mem_range.mpr (by omega))
    · exact mem_leastRootWordDetectionSet_leastRootWordDegreeWithin
        rho b n chi hchi

omit [Fintype X] in
theorem iUnion_finitePlaneNontrivialSet
    (rho : elementaryGroup (Fin 3) (R (X := X)) →* (E ≃ₗᵢ[ℝ] E)) :
    (⋃ s : Finset (Fin 2 × R (X := X)), finitePlaneNontrivialSet rho s) =
      fullPlaneNontrivialSet rho := by
  classical
  ext chi
  constructor
  · intro hchi
    obtain ⟨s, hs⟩ := Set.mem_iUnion.mp hchi
    exact finitePlaneNontrivialSet_subset_fullPlaneNontrivialSet rho s hs
  · intro hchi
    rcases hchi with ⟨q, hq⟩
    apply Set.mem_iUnion.mpr
    refine ⟨({q} : Finset (Fin 2 × R (X := X))), ?_⟩
    exact ⟨q, Finset.mem_singleton_self q, hq⟩

/-- The full moving part of the represented column-plane spectrum is Borel.
Countability comes from the explicit monoid-algebra model of the integral
free algebra, not from an additional assumption. -/
theorem measurableSet_fullPlaneNontrivialSet
    (rho : elementaryGroup (Fin 3) (R (X := X)) →* (E ≃ₗᵢ[ℝ] E)) :
    MeasurableSet (fullPlaneNontrivialSet rho) := by
  rw [← iUnion_finitePlaneNontrivialSet rho]
  exact MeasurableSet.iUnion fun s ↦ measurableSet_finitePlaneNontrivialSet rho s

/-- Evaluation on a finite coefficient family gives an honest
finite-dimensional additive torus. -/
noncomputable def finitePlaneCoordinate
    (rho : elementaryGroup (Fin 3) (R (X := X)) →* (E ≃ₗᵢ[ℝ] E))
    (s : Finset (Fin 2 × R (X := X))) (chi : Spectrum rho) :
    s → AddCircle (1 : ℝ) :=
  fun q ↦ coordinateAngle rho q.1 chi

omit [Fintype X] in
theorem measurable_finitePlaneCoordinate
    (rho : elementaryGroup (Fin 3) (R (X := X)) →* (E ≃ₗᵢ[ℝ] E))
    (s : Finset (Fin 2 × R (X := X))) :
    Measurable (finitePlaneCoordinate rho s) := by
  apply measurable_pi_lambda
  intro q
  exact (continuous_coordinateAngle rho q.1).measurable

omit [Fintype X] in
theorem finitePlaneCoordinate_preimage_punctured
    (rho : elementaryGroup (Fin 3) (R (X := X)) →* (E ≃ₗᵢ[ℝ] E))
    (s : Finset (Fin 2 × R (X := X))) :
    finitePlaneCoordinate rho s ⁻¹'
        (Set.univ \ {(0 : s → AddCircle (1 : ℝ))}) =
      finitePlaneNontrivialSet rho s := by
  classical
  ext chi
  constructor
  · intro hchi
    have hne : finitePlaneCoordinate rho s chi ≠ 0 := by
      intro hzero
      exact hchi.2 (Set.mem_singleton_iff.mpr hzero)
    by_contra hnot
    apply hne
    funext q
    apply (coordinateAngle_eq_zero_iff rho q.1 chi).mpr
    by_contra hq
    apply hnot
    exact ⟨q.1, q.2, hq⟩
  · rintro ⟨q, hqs, hq⟩
    refine ⟨Set.mem_univ _, ?_⟩
    intro hzero
    have hcoordinate := congrFun (Set.mem_singleton_iff.mp hzero) ⟨q, hqs⟩
    change coordinateAngle rho q chi = 0 at hcoordinate
    exact hq ((coordinateAngle_eq_zero_iff rho q chi).mp hcoordinate)

/-- The finite-torus pushforward of the full column-plane spectral measure. -/
noncomputable def finitePlaneMeasure
    (rho : elementaryGroup (Fin 3) (R (X := X)) →* (E ≃ₗᵢ[ℝ] E))
    (z : E) (hz : ‖z‖ = 1)
    (s : Finset (Fin 2 × R (X := X))) :
    Measure (s → AddCircle (1 : ℝ)) :=
  Measure.map (finitePlaneCoordinate rho s)
    (CommutativeStateSpectralMeasure.stateSpectralMeasure
      ((P rho).vectorState (Complexification.mk z 0)
        (norm_mk_zero_eq_one hz)))

omit [Fintype X] in
theorem finitePlaneMeasure_punctured_eq
    (rho : elementaryGroup (Fin 3) (R (X := X)) →* (E ≃ₗᵢ[ℝ] E))
    (z : E) (hz : ‖z‖ = 1)
    (s : Finset (Fin 2 × R (X := X))) :
    (finitePlaneMeasure rho z hz s).real
        (Set.univ \ {(0 : s → AddCircle (1 : ℝ))}) =
      (CommutativeStateSpectralMeasure.stateSpectralMeasure
        ((P rho).vectorState (Complexification.mk z 0)
          (norm_mk_zero_eq_one hz))).real
        (finitePlaneNontrivialSet rho s) := by
  have hpunctured : MeasurableSet
      (Set.univ \ ({(0 : s → AddCircle (1 : ℝ))} :
        Set (s → AddCircle (1 : ℝ)))) :=
    MeasurableSet.univ.diff (measurableSet_singleton 0)
  unfold finitePlaneMeasure
  rw [map_measureReal_apply (measurable_finitePlaneCoordinate rho s) hpunctured]
  rw [finitePlaneCoordinate_preimage_punctured]

omit [Fintype X] in
/-- Every finite-dimensional torus detects only part of the full nontrivial
column-plane support.  Thus all finite-stage mass estimates naturally point
upward toward the full mass. -/
theorem finitePlaneMeasure_punctured_le_fullPlaneNontrivialSet
    (rho : elementaryGroup (Fin 3) (R (X := X)) →* (E ≃ₗᵢ[ℝ] E))
    (z : E) (hz : ‖z‖ = 1)
    (s : Finset (Fin 2 × R (X := X))) :
    (finitePlaneMeasure rho z hz s).real
        (Set.univ \ {(0 : s → AddCircle (1 : ℝ))}) ≤
      (CommutativeStateSpectralMeasure.stateSpectralMeasure
        ((P rho).vectorState (Complexification.mk z 0)
          (norm_mk_zero_eq_one hz))).real
        (fullPlaneNontrivialSet rho) := by
  rw [finitePlaneMeasure_punctured_eq]
  exact measureReal_mono
    (finitePlaneNontrivialSet_subset_fullPlaneNontrivialSet rho s)

omit [Fintype X] in
theorem scalarTorusCoordinate_preimage_punctured
    (rho : elementaryGroup (Fin 3) (R (X := X)) →* (E ≃ₗᵢ[ℝ] E)) :
    scalarTorusCoordinate rho ⁻¹' (Set.univ \ {(0, 0)}) =
      unitRootNontrivialSet rho := by
  classical
  ext chi
  constructor
  · intro hchi
    have hne : scalarTorusCoordinate rho chi ≠ (0, 0) := hchi.2
    have hnotBoth : ¬
        (chi ((P rho).coordinate (0, 1)) = 1 ∧
          chi ((P rho).coordinate (1, 1)) = 1) :=
      (not_congr (scalarTorusCoordinate_eq_zero_iff rho chi)).mp hne
    exact not_and_or.mp hnotBoth
  · intro hchi
    refine ⟨Set.mem_univ _, ?_⟩
    intro hzero
    have hboth := (scalarTorusCoordinate_eq_zero_iff rho chi).mp
      (Set.mem_singleton_iff.mp hzero)
    rcases hchi with hzero0 | hzero1
    · exact hzero0 hboth.1
    · exact hzero1 hboth.2

omit [Fintype X] in
theorem unitRootNontrivialSet_subset_fullPlaneNontrivialSet
    (rho : elementaryGroup (Fin 3) (R (X := X)) →* (E ≃ₗᵢ[ℝ] E)) :
    unitRootNontrivialSet rho ⊆ fullPlaneNontrivialSet rho := by
  intro chi hchi
  rcases hchi with hzero | hone
  · exact ⟨(0, 1), hzero⟩
  · exact ⟨(1, 1), hone⟩

omit [Fintype X] in
/-- The pushed mass away from the scalar origin is exactly the original
spectral mass detected by the two unit roots. -/
theorem scalarTorusMeasure_punctured_eq_unitRootNontrivialSet
    (rho : elementaryGroup (Fin 3) (R (X := X)) →* (E ≃ₗᵢ[ℝ] E))
    (z : E) (hz : ‖z‖ = 1) :
    (scalarTorusMeasure rho z hz).real (Set.univ \ {(0, 0)}) =
      (CommutativeStateSpectralMeasure.stateSpectralMeasure
        ((P rho).vectorState (Complexification.mk z 0)
          (norm_mk_zero_eq_one hz))).real (unitRootNontrivialSet rho) := by
  have hpunctured : MeasurableSet
      (Set.univ \ ({(0, 0)} : Set Torus)) :=
    MeasurableSet.univ.diff (measurableSet_singleton (0, 0))
  unfold scalarTorusMeasure
  rw [map_measureReal_apply (continuous_scalarTorusCoordinate rho).measurable
    hpunctured]
  rw [scalarTorusCoordinate_preimage_punctured]

omit [Fintype X] in
/-- Consequently, the scalar punctured mass is bounded above by the spectral
mass nontrivial on the full column plane.  This is the direction opposite to
the one needed to deduce a full-plane moving-projection bound from the scalar
torus estimate. -/
theorem scalarTorusMeasure_punctured_le_fullPlaneNontrivialSet
    (rho : elementaryGroup (Fin 3) (R (X := X)) →* (E ≃ₗᵢ[ℝ] E))
    (z : E) (hz : ‖z‖ = 1) :
    (scalarTorusMeasure rho z hz).real (Set.univ \ {(0, 0)}) ≤
      (CommutativeStateSpectralMeasure.stateSpectralMeasure
        ((P rho).vectorState (Complexification.mk z 0)
          (norm_mk_zero_eq_one hz))).real (fullPlaneNontrivialSet rho) := by
  rw [scalarTorusMeasure_punctured_eq_unitRootNontrivialSet]
  exact measureReal_mono
    (unitRootNontrivialSet_subset_fullPlaneNontrivialSet rho)

omit [Fintype X] in
theorem integral_firstChordSq_scalarTorusMeasure
    (rho : elementaryGroup (Fin 3) (R (X := X)) →* (E ≃ₗᵢ[ℝ] E))
    (z : E) (hz : ‖z‖ = 1) :
    ∫ p, firstChordSq p ∂scalarTorusMeasure rho z hz =
      ‖rho (columnRoot (0, 1)) z - z‖ ^ 2 := by
  unfold scalarTorusMeasure
  rw [integral_map_of_stronglyMeasurable
    (continuous_scalarTorusCoordinate rho).measurable
    continuous_firstChordSq.stronglyMeasurable]
  calc
    ∫ chi, firstChordSq (scalarTorusCoordinate rho chi)
        ∂CommutativeStateSpectralMeasure.stateSpectralMeasure
          ((P rho).vectorState (Complexification.mk z 0)
            (norm_mk_zero_eq_one hz)) =
      ∫ chi, ‖chi ((P rho).coordinate (0, 1)) - 1‖ ^ 2
        ∂CommutativeStateSpectralMeasure.stateSpectralMeasure
          ((P rho).vectorState (Complexification.mk z 0)
            (norm_mk_zero_eq_one hz)) := by
      apply integral_congr_ae
      filter_upwards [] with chi
      unfold firstChordSq scalarTorusCoordinate
      rw [coordinateAngle_toCircle, coordinateCircle_coe]
    _ = ‖rho (columnRoot (0, 1)) z - z‖ ^ 2 :=
      integral_columnRoot_displacement_sq rho z hz (0, 1)

omit [Fintype X] in
theorem integral_secondChordSq_scalarTorusMeasure
    (rho : elementaryGroup (Fin 3) (R (X := X)) →* (E ≃ₗᵢ[ℝ] E))
    (z : E) (hz : ‖z‖ = 1) :
    ∫ p, secondChordSq p ∂scalarTorusMeasure rho z hz =
      ‖rho (columnRoot (1, 1)) z - z‖ ^ 2 := by
  unfold scalarTorusMeasure
  rw [integral_map_of_stronglyMeasurable
    (continuous_scalarTorusCoordinate rho).measurable
    continuous_secondChordSq.stronglyMeasurable]
  calc
    ∫ chi, secondChordSq (scalarTorusCoordinate rho chi)
        ∂CommutativeStateSpectralMeasure.stateSpectralMeasure
          ((P rho).vectorState (Complexification.mk z 0)
            (norm_mk_zero_eq_one hz)) =
      ∫ chi, ‖chi ((P rho).coordinate (1, 1)) - 1‖ ^ 2
        ∂CommutativeStateSpectralMeasure.stateSpectralMeasure
          ((P rho).vectorState (Complexification.mk z 0)
            (norm_mk_zero_eq_one hz)) := by
      apply integral_congr_ae
      filter_upwards [] with chi
      unfold secondChordSq scalarTorusCoordinate
      rw [coordinateAngle_toCircle, coordinateCircle_coe]
    _ = ‖rho (columnRoot (1, 1)) z - z‖ ^ 2 :=
      integral_columnRoot_displacement_sq rho z hz (1, 1)

private theorem columnRoot_zero_one_mem_integralControlSet :
    columnRoot ((0 : Fin 2), (1 : R (X := X))) ∈ integralControlSet X := by
  let a : A2Root := ⟨((0 : Fin 3), (2 : Fin 3)), by decide⟩
  have hm := integralControlElement_mem X (a, none)
  simpa [a, integralControlElement, integralControlCoefficient, columnRoot,
    columnSource] using hm

private theorem columnRoot_one_one_mem_integralControlSet :
    columnRoot ((1 : Fin 2), (1 : R (X := X))) ∈ integralControlSet X := by
  let a : A2Root := ⟨((1 : Fin 3), (2 : Fin 3)), by decide⟩
  have hm := integralControlElement_mem X (a, none)
  simpa [a, integralControlElement, integralControlCoefficient, columnRoot,
    columnSource] using hm

theorem scalarTorusMeasure_verticalOuter_le
    (rho : elementaryGroup (Fin 3) (R (X := X)) →* (E ≃ₗᵢ[ℝ] E))
    (z : E) (hz : ‖z‖ = 1) (delta : ℝ)
    (hdelta : 0 < delta)
    (hnear : ∀ s ∈ integralControlSet X, ‖rho s z - z‖ < delta) :
    (scalarTorusMeasure rho z hz).real verticalOuter ≤ delta ^ 2 / 2 := by
  have hroot := hnear _ columnRoot_zero_one_mem_integralControlSet
  have hintegral := two_mul_measureReal_verticalOuter_le_integral_firstChordSq
    (scalarTorusMeasure rho z hz)
  rw [integral_firstChordSq_scalarTorusMeasure rho z hz] at hintegral
  have hsq : ‖rho (columnRoot (0, 1)) z - z‖ ^ 2 < delta ^ 2 :=
    (sq_lt_sq₀ (norm_nonneg _) hdelta.le).mpr hroot
  linarith

theorem scalarTorusMeasure_horizontalOuter_le
    (rho : elementaryGroup (Fin 3) (R (X := X)) →* (E ≃ₗᵢ[ℝ] E))
    (z : E) (hz : ‖z‖ = 1) (delta : ℝ)
    (hdelta : 0 < delta)
    (hnear : ∀ s ∈ integralControlSet X, ‖rho s z - z‖ < delta) :
    (scalarTorusMeasure rho z hz).real horizontalOuter ≤ delta ^ 2 / 2 := by
  have hroot := hnear _ columnRoot_one_one_mem_integralControlSet
  have hintegral :=
    two_mul_measureReal_horizontalOuter_le_integral_secondChordSq
      (scalarTorusMeasure rho z hz)
  rw [integral_secondChordSq_scalarTorusMeasure rho z hz] at hintegral
  have hsq : ‖rho (columnRoot (1, 1)) z - z‖ ^ 2 < delta ^ 2 :=
    (sq_lt_sq₀ (norm_nonneg _) hdelta.le).mpr hroot
  linarith

/-- The scalar torus spectral measure has uniformly small mass away from its
trivial character. -/
theorem scalarTorusMeasure_punctured_mass_le
    (rho : elementaryGroup (Fin 3) (R (X := X)) →* (E ≃ₗᵢ[ℝ] E))
    (z : E) (hz : ‖z‖ = 1) (delta : ℝ)
    (hdelta : 0 < delta)
    (hnear : ∀ s ∈ integralControlSet X, ‖rho s z - z‖ < delta) :
    (scalarTorusMeasure rho z hz).real (Set.univ \ {(0, 0)}) ≤
      (2 + Real.sqrt 10) ^ 2 * delta ^ 2 := by
  apply total_mass_le_of_four_shear_quasiInvariant
    (scalarTorusMeasure rho z hz) hdelta.le
    (scalarTorusMeasure_verticalOuter_le rho z hz delta hdelta hnear)
    (scalarTorusMeasure_horizontalOuter_le rho z hz delta hdelta hnear)
  · exact scalarTorusMeasure_measurableQuasiInvariantAtScale_g12Plus
      X rho z hz delta hdelta hnear
  · exact scalarTorusMeasure_measurableQuasiInvariantAtScale_g12Minus
      X rho z hz delta hdelta hnear
  · exact scalarTorusMeasure_measurableQuasiInvariantAtScale_g21Plus
      X rho z hz delta hdelta hnear
  · exact scalarTorusMeasure_measurableQuasiInvariantAtScale_g21Minus
      X rho z hz delta hdelta hnear

end
end IntegralColumnPlaneSpectralMassBound
end GroupApproximation

open GroupApproximation.IntegralColumnPlaneSpectralMassBound

#audit_axioms scalarTorusMeasure_verticalOuter_le
#audit_axioms scalarTorusMeasure_horizontalOuter_le
#audit_axioms scalarTorusMeasure_punctured_mass_le
#audit_axioms card_integralFiniteCoefficientClosure_le
#audit_axioms exists_controlCoefficient_mul_wordMonomial
#audit_axioms integralFiniteCoefficientClosure_wordCoordinateSet_subset
#audit_axioms finitePlaneNontrivialSet_of_controlled_characterAction_upper_mem
#audit_axioms finitePlaneNontrivialSet_of_controlled_characterAction_lower_mem
#audit_axioms wordCoordinateNontrivial_of_controlled_characterAction_upper_mem
#audit_axioms wordCoordinateNontrivial_of_controlled_characterAction_lower_mem
#audit_axioms measurableSet_leastRootWordDetectionSet
#audit_axioms disjoint_leastRootWordDetectionSet
#audit_axioms iUnion_leastRootWordDetectionSet_range
#audit_axioms measurableSet_fullPlaneNontrivialSet
