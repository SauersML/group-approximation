import STW.Actual.FockPair
import GroupApproximation.Analysis.CStarQuotientHom
import GroupApproximation.Analysis.VoiculescuUnitStrongLimit

/-!
# The Cuntz generators in the Calkin algebra

The two Fock prefix shifts are genuine orthogonal isometries in `B(FockSpace)`.
Their range projections cover every non-vacuum word.  The missing vacuum is a
rank-one projection, hence compact, so it vanishes in the Calkin quotient.
Thus the two quotient generators satisfy all Cuntz relations exactly.
-/

namespace STW.Actual

noncomputable section

open GroupApproximation

abbrev FockCalkin := CalkinAlgebra.CalkinQuotient FockSpace

/-- The quotient map `B(FockSpace) → Q(FockSpace)` as a star-algebra hom. -/
noncomputable def essentialStar :
    (FockSpace →L[ℂ] FockSpace) →⋆ₐ[ℂ] FockCalkin :=
  CStarTensor.quotientStarMk (CalkinAlgebra.compactIdeal FockSpace)

@[simp] theorem essentialStar_apply (T : FockSpace →L[ℂ] FockSpace) :
    essentialStar T = CalkinAlgebra.essential FockSpace T := rfl

/-- The two Cuntz generators in the Calkin algebra. -/
def calkinPrefix (b : Bool) : FockCalkin := essentialStar (prefixOp b)

/-- Each Calkin prefix generator is an isometry. -/
theorem calkinPrefix_star_mul_self (b : Bool) :
    star (calkinPrefix b) * calkinPrefix b = 1 := by
  rw [← map_star (essentialStar) (prefixOp b), ← map_mul]
  rw [prefixOp_star_mul_self]
  exact map_one essentialStar

/-- Distinct Calkin prefix generators have orthogonal ranges. -/
theorem calkinPrefix_star_mul_of_ne {b c : Bool} (hbc : b ≠ c) :
    star (calkinPrefix b) * calkinPrefix c = 0 := by
  rw [← map_star (essentialStar) (prefixOp b), ← map_mul]
  rw [prefixOp_star_mul_of_ne hbc]
  exact map_zero essentialStar

@[simp] theorem calkinPrefix_star_mul_false_true :
    star (calkinPrefix false) * calkinPrefix true = 0 :=
  calkinPrefix_star_mul_of_ne (by decide)

@[simp] theorem calkinPrefix_star_mul_true_false :
    star (calkinPrefix true) * calkinPrefix false = 0 :=
  calkinPrefix_star_mul_of_ne (by decide)

/-! ## The vacuum is the unique range defect -/

/-- Range projection of the prefix isometry. -/
def prefixRangeProjection (b : Bool) : FockSpace →L[ℂ] FockSpace :=
  prefixOp b * star (prefixOp b)

/-- On a word beginning with `b`, the range projection is the identity. -/
theorem prefixRangeProjection_apply_prefix (b : Bool) (f : FockSpace)
    (w : FockIndex) :
    prefixRangeProjection b f (prefixMap b w) = f (prefixMap b w) := by
  change prefixOp b (star (prefixOp b) f) (prefixMap b w) = _
  rw [ContinuousLinearMap.star_eq_adjoint, adjoint_prefixOp_apply,
    prefixOp_apply, prefixFun_apply_prefix, suffixFun_apply]

/-- Away from words beginning with `b`, the range projection vanishes. -/
theorem prefixRangeProjection_apply_off (b : Bool) (f : FockSpace)
    {y : FockIndex} (hy : ¬ ∃ w, prefixMap b w = y) :
    prefixRangeProjection b f y = 0 := by
  change prefixOp b (star (prefixOp b) f) y = 0
  rw [prefixOp_apply]
  exact prefixFun_apply_off b _ hy

/-- The Fock vacuum vector. -/
def vacuum : FockSpace := lp.single 2 ([] : FockIndex) (1 : ℂ)

/-- Pairing against the vacuum reads the empty-word coordinate. -/
@[simp] theorem inner_vacuum (f : FockSpace) : ⟪vacuum, f⟫_ℂ = f [] := by
  rw [vacuum, lp.inner_single_left]
  simp

/-- Rank-one projection onto the vacuum line. -/
def vacuumProjection : FockSpace →L[ℂ] FockSpace :=
  ShulmanFill.rankOneSelf vacuum

@[simp] theorem vacuumProjection_apply_empty (f : FockSpace) :
    vacuumProjection f [] = f [] := by
  rw [vacuumProjection, ShulmanFill.rankOneSelf_apply, inner_vacuum]
  change (f [] • vacuum) [] = f []
  rw [lp.coeFn_smul, Pi.smul_apply, vacuum, lp.single_apply_self]
  simp

@[simp] theorem vacuumProjection_apply_cons (f : FockSpace) (b : Bool)
    (w : FockIndex) : vacuumProjection f (b :: w) = 0 := by
  rw [vacuumProjection, ShulmanFill.rankOneSelf_apply, inner_vacuum]
  change (f [] • vacuum) (b :: w) = 0
  rw [lp.coeFn_smul, Pi.smul_apply, vacuum]
  rw [lp.single_apply_ne]
  · simp
  · simp

/-- The operator left over after the two range projections. -/
def fockDefect : FockSpace →L[ℂ] FockSpace :=
  1 - prefixRangeProjection false - prefixRangeProjection true

/-- The range defect is exactly the rank-one vacuum projection. -/
theorem fockDefect_eq_vacuumProjection : fockDefect = vacuumProjection := by
  ext f
  apply lp.ext
  funext y
  cases y with
  | nil =>
      have hfalse : ¬ ∃ w, prefixMap false w = ([] : FockIndex) := by simp [prefixMap]
      have htrue : ¬ ∃ w, prefixMap true w = ([] : FockIndex) := by simp [prefixMap]
      change f [] - prefixRangeProjection false f [] -
          prefixRangeProjection true f [] = vacuumProjection f []
      rw [prefixRangeProjection_apply_off false f hfalse,
        prefixRangeProjection_apply_off true f htrue, vacuumProjection_apply_empty]
      simp
  | cons b w =>
      cases b with
      | false =>
          have hoff : ¬ ∃ z, prefixMap true z = false :: w := by
            rintro ⟨z, hz⟩
            simp [prefixMap] at hz
          change f (false :: w) - prefixRangeProjection false f (false :: w) -
              prefixRangeProjection true f (false :: w) = vacuumProjection f (false :: w)
          rw [prefixRangeProjection_apply_prefix false f w,
            prefixRangeProjection_apply_off true f hoff, vacuumProjection_apply_cons]
          simp
      | true =>
          have hoff : ¬ ∃ z, prefixMap false z = true :: w := by
            rintro ⟨z, hz⟩
            simp [prefixMap] at hz
          change f (true :: w) - prefixRangeProjection false f (true :: w) -
              prefixRangeProjection true f (true :: w) = vacuumProjection f (true :: w)
          rw [prefixRangeProjection_apply_off false f hoff,
            prefixRangeProjection_apply_prefix true f w, vacuumProjection_apply_cons]
          simp

/-- Consequently the defect is compact. -/
theorem isCompactOperator_fockDefect : IsCompactOperator fockDefect := by
  rw [fockDefect_eq_vacuumProjection, vacuumProjection]
  exact ShulmanFill.isCompactOperator_rankOneSelf vacuum

/-- The vacuum defect vanishes in the Calkin quotient. -/
theorem essentialStar_fockDefect : essentialStar fockDefect = 0 := by
  rw [essentialStar_apply]
  exact (CalkinAlgebra.essential_eq_zero_iff FockSpace fockDefect).2
    isCompactOperator_fockDefect

/-- **The fourth Cuntz relation.**  The two range projections sum to one in the
Calkin algebra. -/
theorem calkinPrefix_range_sum :
    calkinPrefix false * star (calkinPrefix false) +
      calkinPrefix true * star (calkinPrefix true) = 1 := by
  have hzero :
      1 - calkinPrefix false * star (calkinPrefix false) -
        calkinPrefix true * star (calkinPrefix true) = 0 := by
    simpa [fockDefect, prefixRangeProjection, calkinPrefix] using essentialStar_fockDefect
  calc
    calkinPrefix false * star (calkinPrefix false) +
        calkinPrefix true * star (calkinPrefix true)
        = 1 - (1 - calkinPrefix false * star (calkinPrefix false) -
          calkinPrefix true * star (calkinPrefix true)) := by abel
    _ = 1 := by rw [hzero]; simp

end

end STW.Actual
