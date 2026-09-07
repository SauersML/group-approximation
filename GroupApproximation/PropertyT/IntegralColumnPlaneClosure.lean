import GroupApproximation.PropertyT.IntegralColumnPlaneSpanning
import GroupApproximation.PropertyT.EJZIntegralGeneralRankReduction
import GroupApproximation.Meta.AxiomGuard

/-!
# Closing the integral column-plane estimate

The four inequalities of the preceding modules form a closed system at each
degree stage.  Writing `A, B, C, D` for the masses of the four nonzero regions
of the column-plane spectral measure of an almost invariant unit vector, and
`K = sqrt |X| * delta`:

```
sqrt (A + B) ≤ sqrt (C + D) + K       (lower generator shear)
sqrt (C + B) ≤ sqrt (A + D) + K       (upper generator shear)
sqrt A ≤ sqrt B + delta               (lower unit shear)
sqrt C ≤ sqrt B + delta               (upper unit shear)
D ≤ (2 + sqrt 10)² delta²             (scalar torus estimate)
```

Adding the first two cancels `A` and `C` and bounds `B` by `D` plus the shear
errors; the unit inequalities then bound `A` and `C` by `B`.  So the whole
nonzero mass is `O(delta²)` with a constant depending only on the size of the
alphabet, uniformly in the degree stage.

That is the estimate the integral route was missing.  Since word monomials
span each degree stage, it bounds the displacement of the vector by every
column root, hence -- through the reindexing symmetry and the equivalences of
`IntegralColumnPlaneReduction` -- gives `ColumnPlaneMassBound` over
`ℤ⟨X⟩`, and therefore, via `printedEJZColumnPlaneReduction`, property `(T)`
for `EL_n` of every finitely generated unital ring in every characteristic and
every rank `n ≥ 3`.
-/

namespace GroupApproximation
namespace IntegralColumnPlaneClosure

open Set MeasureTheory WeakDual
open IntegralCharacterMass
open IntegralColumnPlaneSpectralMeasure
open IntegralColumnPlaneSpectralShear
open IntegralColumnPlaneSpectralTorus
open IntegralColumnPlaneSpectralMassBound
open IntegralColumnPlaneReduction
open IntegralColumnPlaneRootReduction
open IntegralGeneratorShearDescent
open IntegralGeneratorShearSelector
open IntegralGeneratorShearMass
open IntegralGeneratorShearDescentMass
open IntegralColumnPlaneSpanning
open FreeAlgebraDegree

noncomputable section

universe u v

/-! ### The real arithmetic of the closed system -/

theorem sqrt_add_le_add_sqrt {x y : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y) :
    Real.sqrt (x + y) ≤ Real.sqrt x + Real.sqrt y := by
  have hsq : x + y ≤ (Real.sqrt x + Real.sqrt y) ^ 2 := by
    have h1 := Real.sq_sqrt hx
    have h2 := Real.sq_sqrt hy
    nlinarith [Real.sqrt_nonneg x, Real.sqrt_nonneg y]
  calc Real.sqrt (x + y) ≤ Real.sqrt ((Real.sqrt x + Real.sqrt y) ^ 2) :=
        Real.sqrt_le_sqrt hsq
    _ = Real.sqrt x + Real.sqrt y :=
        Real.sqrt_sq (by positivity)

/-- The polynomial core of the closed system, with no square roots left. -/
theorem total_le_of_polynomial_system {p q r s K delta : ℝ}
    (hpn : 0 ≤ p) (hqn : 0 ≤ q) (_hrn : 0 ≤ r) (hsn : 0 ≤ s)
    (hK : 0 ≤ K) (hdelta : 0 ≤ delta)
    (e1 : p ^ 2 + q ^ 2 ≤ (r + s + K) ^ 2)
    (e2 : r ^ 2 + q ^ 2 ≤ (p + s + K) ^ 2)
    (h3 : p ≤ q + delta) (h4 : r ≤ q + delta) :
    p ^ 2 + q ^ 2 + r ^ 2 + s ^ 2 ≤ 42 * (s + K + delta) ^ 2 := by
  have hU : (0 : ℝ) ≤ s + K := by linarith
  have hV : (0 : ℝ) ≤ s + K + delta := by linarith
  have hsum : 2 * q ^ 2 ≤ 2 * (s + K) ^ 2 + 2 * (s + K) * (p + r) := by
    nlinarith [e1, e2]
  have hpr : p + r ≤ 2 * q + 2 * delta := by linarith
  have hmul : (s + K) * (p + r) ≤ (s + K) * (2 * q + 2 * delta) :=
    mul_le_mul_of_nonneg_left hpr hU
  have hqsq : q ^ 2 ≤ (s + K) ^ 2 + (s + K) * (2 * q + 2 * delta) := by
    linarith
  have hUV : s + K ≤ s + K + delta := by linarith
  have hq1 : (s + K) ^ 2 ≤ (s + K + delta) ^ 2 := by nlinarith
  have hq2 : (s + K) * (2 * q) ≤ (s + K + delta) * (2 * q) := by nlinarith
  have hq3 : (s + K) * (2 * delta) ≤ 2 * (s + K + delta) ^ 2 := by nlinarith
  have hqV : q ^ 2 ≤ 3 * (s + K + delta) ^ 2 + 2 * (s + K + delta) * q := by
    nlinarith
  have hq3V : q ≤ 3 * (s + K + delta) := by
    by_cases hle : q ≤ 3 * (s + K + delta)
    · exact hle
    · exfalso
      have hlt : 3 * (s + K + delta) < q := by
        exact lt_of_not_ge hle
      have hpos1 : 0 < q - 3 * (s + K + delta) := by linarith
      have hpos2 : 0 < q + (s + K + delta) := by linarith
      nlinarith [mul_pos hpos1 hpos2]
  have hp4V : p ≤ 4 * (s + K + delta) := by linarith
  have hr4V : r ≤ 4 * (s + K + delta) := by linarith
  have hsV : s ≤ s + K + delta := by linarith
  have hp2 : p ^ 2 ≤ 16 * (s + K + delta) ^ 2 := by nlinarith
  have hq2' : q ^ 2 ≤ 9 * (s + K + delta) ^ 2 := by nlinarith
  have hr2 : r ^ 2 ≤ 16 * (s + K + delta) ^ 2 := by nlinarith
  have hs2 : s ^ 2 ≤ (s + K + delta) ^ 2 := by nlinarith
  linarith

/-- **The closed system.**  Four masses obeying the two descent inequalities
and the two fold inequalities have total size at most `42 (sqrt d + K + delta)²`.

The `42` is not free to move upward.  It is coupled to the `13` in
`norm_columnRoot_displacement_le_of_unit`, because the passage from the mass
bound to a displacement bound squares and pays a factor four:
`4 * 42 = 168 ≤ 169 = 13 ^ 2`, a margin of one.  Loosening the `42` to `43`
gives `4 * 43 = 172 > 169` and breaks the `13`, which would have to become
`14`.  Tightening it is harmless. -/
theorem total_le_of_closed_system {a b c d K delta : ℝ}
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) (hd : 0 ≤ d)
    (hK : 0 ≤ K) (hdelta : 0 ≤ delta)
    (h1 : Real.sqrt (a + b) ≤ Real.sqrt (c + d) + K)
    (h2 : Real.sqrt (c + b) ≤ Real.sqrt (a + d) + K)
    (h3 : Real.sqrt a ≤ Real.sqrt b + delta)
    (h4 : Real.sqrt c ≤ Real.sqrt b + delta) :
    a + b + c + d ≤ 42 * (Real.sqrt d + K + delta) ^ 2 := by
  have hpa : Real.sqrt a ^ 2 = a := Real.sq_sqrt ha
  have hqb : Real.sqrt b ^ 2 = b := Real.sq_sqrt hb
  have hrc : Real.sqrt c ^ 2 = c := Real.sq_sqrt hc
  have hsd : Real.sqrt d ^ 2 = d := Real.sq_sqrt hd
  have hab : Real.sqrt (a + b) ≤ Real.sqrt c + Real.sqrt d + K := by
    refine h1.trans ?_
    have := sqrt_add_le_add_sqrt hc hd
    linarith
  have hcb : Real.sqrt (c + b) ≤ Real.sqrt a + Real.sqrt d + K := by
    refine h2.trans ?_
    have := sqrt_add_le_add_sqrt ha hd
    linarith
  have e1 : Real.sqrt a ^ 2 + Real.sqrt b ^ 2 ≤
      (Real.sqrt c + Real.sqrt d + K) ^ 2 := by
    have hnn : (0 : ℝ) ≤ a + b := by linarith
    have hsq : Real.sqrt (a + b) ^ 2 = a + b := Real.sq_sqrt hnn
    nlinarith [Real.sqrt_nonneg (a + b), Real.sqrt_nonneg c, Real.sqrt_nonneg d]
  have e2 : Real.sqrt c ^ 2 + Real.sqrt b ^ 2 ≤
      (Real.sqrt a + Real.sqrt d + K) ^ 2 := by
    have hnn : (0 : ℝ) ≤ c + b := by linarith
    have hsq : Real.sqrt (c + b) ^ 2 = c + b := Real.sq_sqrt hnn
    nlinarith [Real.sqrt_nonneg (c + b), Real.sqrt_nonneg a, Real.sqrt_nonneg d]
  have hmain := total_le_of_polynomial_system (Real.sqrt_nonneg a)
    (Real.sqrt_nonneg b) (Real.sqrt_nonneg c) (Real.sqrt_nonneg d) hK hdelta
    e1 e2 h3 h4
  linarith

/-! ### The per-stage mass bound -/

variable {E : Type v} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [CompleteSpace E]
variable {X : Type u} [Fintype X]
variable (rho : elementaryGroup (Fin 3) (FreeAlgebra ℤ X) →* (E ≃ₗᵢ[ℝ] E))

noncomputable local instance columnPlaneCharacterMeasurableSpaceCl :
    MeasurableSpace (characterSpace ℂ (representedColumnPlane rho).algebra) :=
  borel _

local instance columnPlaneCharacterBorelSpaceCl :
    BorelSpace (characterSpace ℂ (representedColumnPlane rho).algebra) :=
  ⟨rfl⟩

noncomputable local instance columnPlaneSpectralMeasureIsFiniteCl
    (z : E) (hz : ‖z‖ = 1) :
    IsFiniteMeasure (columnPlaneSpectralMeasure rho z hz) := by
  unfold columnPlaneSpectralMeasure
  infer_instance

/-- The mass of the region `D` is bounded by the already-proved scalar torus
estimate. -/
theorem measureReal_regionD_le
    (z : E) (hz : ‖z‖ = 1) (n : ℕ) (delta : ℝ) (hdelta : 0 < delta)
    (hnear : ∀ s ∈ integralControlSet X, ‖rho s z - z‖ < delta) :
    (columnPlaneSpectralMeasure rho z hz).real
        (wordPairRegionSet rho n .D) ≤ (2 + Real.sqrt 10) ^ 2 * delta ^ 2 := by
  rw [wordPairRegionSet_D_eq_unitRootNontrivialSet rho n]
  have hkey := scalarTorusMeasure_punctured_mass_le rho z hz delta hdelta hnear
  rw [scalarTorusMeasure_punctured_eq_unitRootNontrivialSet rho z hz] at hkey
  exact hkey

/-- The four nonzero regions are pairwise disjoint, so the mass of their union
is the sum of the four masses. -/
theorem measureReal_regionUnion_eq
    (z : E) (hz : ‖z‖ = 1) (n : ℕ) :
    (columnPlaneSpectralMeasure rho z hz).real (regionUnion rho n) =
      (columnPlaneSpectralMeasure rho z hz).real (wordPairRegionSet rho n .A) +
        (columnPlaneSpectralMeasure rho z hz).real
          (wordPairRegionSet rho n .B) +
        (columnPlaneSpectralMeasure rho z hz).real
          (wordPairRegionSet rho n .C) +
        (columnPlaneSpectralMeasure rho z hz).real
          (wordPairRegionSet rho n .D) := by
  have hAB : Disjoint (wordPairRegionSet rho n .A)
      (wordPairRegionSet rho n .B) := disjoint_wordPairRegionSet rho n (by decide)
  have hABC : Disjoint (wordPairRegionSet rho n .A ∪ wordPairRegionSet rho n .B)
      (wordPairRegionSet rho n .C) := by
    rw [Set.disjoint_union_left]
    exact ⟨disjoint_wordPairRegionSet rho n (by decide),
      disjoint_wordPairRegionSet rho n (by decide)⟩
  have hABCD : Disjoint ((wordPairRegionSet rho n .A ∪
      wordPairRegionSet rho n .B) ∪ wordPairRegionSet rho n .C)
      (wordPairRegionSet rho n .D) := by
    rw [Set.disjoint_union_left, Set.disjoint_union_left]
    exact ⟨⟨disjoint_wordPairRegionSet rho n (by decide),
      disjoint_wordPairRegionSet rho n (by decide)⟩,
      disjoint_wordPairRegionSet rho n (by decide)⟩
  rw [regionUnion,
    measureReal_union hABCD (measurableSet_wordPairRegionSet rho n .D),
    measureReal_union hABC (measurableSet_wordPairRegionSet rho n .C),
    measureReal_union hAB (measurableSet_wordPairRegionSet rho n .B)]

theorem measureReal_regionPair_eq
    (z : E) (hz : ‖z‖ = 1) (n : ℕ) {r s : WordPairRegion} (hrs : r ≠ s) :
    (columnPlaneSpectralMeasure rho z hz).real
        (wordPairRegionSet rho n r ∪ wordPairRegionSet rho n s) =
      (columnPlaneSpectralMeasure rho z hz).real (wordPairRegionSet rho n r) +
        (columnPlaneSpectralMeasure rho z hz).real
          (wordPairRegionSet rho n s) :=
  measureReal_union (disjoint_wordPairRegionSet rho n hrs)
    (measurableSet_wordPairRegionSet rho n s)

/-- **The per-stage moving mass bound.**  Uniform in the degree stage. -/
theorem measureReal_regionUnion_le
    (z : E) (hz : ‖z‖ = 1) (n : ℕ) (delta : ℝ) (hdelta : 0 < delta)
    (hnear : ∀ s ∈ integralControlSet X, ‖rho s z - z‖ < delta) :
    (columnPlaneSpectralMeasure rho z hz).real (regionUnion rho n) ≤
      42 * ((Real.sqrt (Fintype.card X) + 7) * delta) ^ 2 := by
  have h1 := sqrt_measureReal_regionAB_le rho z hz n delta hdelta hnear
  rw [measureReal_regionPair_eq rho z hz n
      (by decide : (WordPairRegion.A) ≠ WordPairRegion.B),
    measureReal_regionPair_eq rho z hz n
      (by decide : (WordPairRegion.C) ≠ WordPairRegion.D)] at h1
  have h2 := sqrt_measureReal_regionCB_le rho z hz n delta hdelta hnear
  rw [measureReal_regionPair_eq rho z hz n
      (by decide : (WordPairRegion.C) ≠ WordPairRegion.B),
    measureReal_regionPair_eq rho z hz n
      (by decide : (WordPairRegion.A) ≠ WordPairRegion.D)] at h2
  have h3 := sqrt_measureReal_regionA_le_regionB rho z hz n delta hdelta hnear
  have h4 := sqrt_measureReal_regionC_le_regionB rho z hz n delta hdelta hnear
  have hD := measureReal_regionD_le rho z hz n delta hdelta hnear
  rw [measureReal_regionUnion_eq rho z hz n]
  set a := (columnPlaneSpectralMeasure rho z hz).real
    (wordPairRegionSet rho n .A) with ha
  set b := (columnPlaneSpectralMeasure rho z hz).real
    (wordPairRegionSet rho n .B) with hb
  set c := (columnPlaneSpectralMeasure rho z hz).real
    (wordPairRegionSet rho n .C) with hc
  set d := (columnPlaneSpectralMeasure rho z hz).real
    (wordPairRegionSet rho n .D) with hd
  have han : 0 ≤ a := measureReal_nonneg
  have hbn : 0 ≤ b := measureReal_nonneg
  have hcn : 0 ≤ c := measureReal_nonneg
  have hdn : 0 ≤ d := measureReal_nonneg
  have hsd : Real.sqrt d ≤ 6 * delta := by
    have h10 : Real.sqrt 10 ≤ 4 := by
      rw [show (4 : ℝ) = Real.sqrt 16 by
        rw [show (16 : ℝ) = 4 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]]
      exact Real.sqrt_le_sqrt (by norm_num)
    have hsq : (2 + Real.sqrt 10) ^ 2 ≤ 36 := by nlinarith [Real.sqrt_nonneg 10]
    have hbound : d ≤ (6 * delta) ^ 2 := by nlinarith [sq_nonneg delta, hD, hsq]
    calc Real.sqrt d ≤ Real.sqrt ((6 * delta) ^ 2) := Real.sqrt_le_sqrt hbound
      _ = 6 * delta := Real.sqrt_sq (by positivity)
  have htotal := total_le_of_closed_system han hbn hcn hdn
    (by positivity : (0 : ℝ) ≤ Real.sqrt (Fintype.card X : ℝ) * delta)
    hdelta.le h1 h2 h3 h4
  refine htotal.trans ?_
  have hVnn : (0 : ℝ) ≤ Real.sqrt d +
      Real.sqrt (Fintype.card X : ℝ) * delta + delta := by positivity
  have hVle : Real.sqrt d + Real.sqrt (Fintype.card X : ℝ) * delta + delta ≤
      (Real.sqrt (Fintype.card X) + 7) * delta := by nlinarith
  nlinarith [hVnn, hVle]

/-! ### From the mass bound to the displacement bound -/

omit [Fintype X] in
theorem norm_coordinate_eq_one
    (q : Fin 2 × FreeAlgebra ℤ X)
    (chi : characterSpace ℂ (representedColumnPlane rho).algebra) :
    ‖chi ((representedColumnPlane rho).coordinate q)‖ = 1 := by
  exact (coordinateCircle rho q chi).norm_coe

omit [Fintype X] in
/-- The squared displacement by a column root is at most four times the mass
of the characters that detect its coefficient. -/
theorem norm_columnRoot_displacement_sq_le
    (z : E) (hz : ‖z‖ = 1) (q : Fin 2 × FreeAlgebra ℤ X) :
    ‖rho (columnRoot q) z - z‖ ^ 2 ≤
      4 * (columnPlaneSpectralMeasure rho z hz).real
        {chi : characterSpace ℂ (representedColumnPlane rho).algebra |
          coordinateAngle rho q chi ≠ 0} := by
  classical
  set S : Set (characterSpace ℂ (representedColumnPlane rho).algebra) :=
    {chi | coordinateAngle rho q chi ≠ 0} with hS
  have hSmeas : MeasurableSet S := measurableSet_coordinateAngle_ne_zero rho q
  have hcont : Continuous (fun chi : characterSpace ℂ
      (representedColumnPlane rho).algebra ↦
        ‖chi ((representedColumnPlane rho).coordinate q) - 1‖ ^ 2) := by
    have hbase : Continuous (fun chi : characterSpace ℂ
        (representedColumnPlane rho).algebra ↦
          chi ((representedColumnPlane rho).coordinate q)) :=
      ((gelfandStarTransform (representedColumnPlane rho).algebra)
        ((representedColumnPlane rho).coordinate q)).continuous
    exact ((hbase.sub continuous_const).norm).pow 2
  have hint1 : Integrable (fun chi : characterSpace ℂ
      (representedColumnPlane rho).algebra ↦
        ‖chi ((representedColumnPlane rho).coordinate q) - 1‖ ^ 2)
      (columnPlaneSpectralMeasure rho z hz) :=
    hcont.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hint2 : Integrable (S.indicator fun _ ↦ (4 : ℝ))
      (columnPlaneSpectralMeasure rho z hz) :=
    (integrable_const (4 : ℝ)).indicator hSmeas
  have hpoint : ∀ chi, ‖chi ((representedColumnPlane rho).coordinate q) - 1‖ ^ 2
      ≤ S.indicator (fun _ ↦ (4 : ℝ)) chi := by
    intro chi
    by_cases hchi : chi ∈ S
    · rw [Set.indicator_of_mem hchi]
      have hnorm := norm_coordinate_eq_one rho q chi
      have hle : ‖chi ((representedColumnPlane rho).coordinate q) - 1‖ ≤ 2 := by
        calc ‖chi ((representedColumnPlane rho).coordinate q) - 1‖ ≤
            ‖chi ((representedColumnPlane rho).coordinate q)‖ + ‖(1 : ℂ)‖ :=
              norm_sub_le _ _
          _ = 2 := by rw [hnorm, norm_one]; norm_num
      nlinarith [norm_nonneg (chi ((representedColumnPlane rho).coordinate q) - 1)]
    · rw [Set.indicator_of_notMem hchi]
      have hone : chi ((representedColumnPlane rho).coordinate q) = 1 := by
        by_contra hne
        exact hchi (fun hzero ↦ hne
          ((coordinateAngle_eq_zero_iff rho q chi).mp hzero))
      rw [hone, sub_self, norm_zero]
      norm_num
  have hmono := integral_mono hint1 hint2 hpoint
  rw [integral_indicator_const (4 : ℝ) hSmeas, smul_eq_mul, mul_comm] at hmono
  rw [← integral_columnRoot_displacement_sq rho z hz q]
  exact hmono

/-- **The displacement bound for a unit vector.**

The `13` is `⌈√168⌉` and is tight against the mass constant.
`norm_columnRoot_displacement_sq_le` pays a factor four on the `42` of
`measureReal_regionUnion_le`, and `4 * 42 = 168 ≤ 169 = 13 ^ 2` with a margin
of one, so any increase of that `42` forces this constant up as well. -/
theorem norm_columnRoot_displacement_le_of_unit
    (z : E) (hz : ‖z‖ = 1) (b : Fin 2) (a : FreeAlgebra ℤ X)
    (delta : ℝ) (hdelta : 0 < delta)
    (hnear : ∀ s ∈ integralControlSet X, ‖rho s z - z‖ < delta) :
    ‖rho (columnRoot (b, a)) z - z‖ ≤
      13 * (Real.sqrt (Fintype.card X) + 7) * delta := by
  obtain ⟨n, hn⟩ := exists_mem_degreeLE X ℤ a
  have hmass : (columnPlaneSpectralMeasure rho z hz).real
      {chi : characterSpace ℂ (representedColumnPlane rho).algebra |
        coordinateAngle rho ((b, a)) chi ≠ 0} ≤
      42 * ((Real.sqrt (Fintype.card X) + 7) * delta) ^ 2 :=
    le_trans
      (measureReal_mono
        (coordinateAngle_ne_zero_subset_regionUnion rho b n a hn))
      (measureReal_regionUnion_le rho z hz n delta hdelta hnear)
  have hsq := norm_columnRoot_displacement_sq_le rho z hz ((b, a))
  have hbound : ‖rho (columnRoot ((b, a))) z - z‖ ^ 2 ≤
      (13 * (Real.sqrt (Fintype.card X) + 7) * delta) ^ 2 := by
    have hnn : (0 : ℝ) ≤ Real.sqrt (Fintype.card X) := Real.sqrt_nonneg _
    nlinarith [hsq, hmass, hdelta.le]
  have hrhs : (0 : ℝ) ≤ 13 * (Real.sqrt (Fintype.card X) + 7) * delta := by
    have : (0 : ℝ) ≤ Real.sqrt (Fintype.card X) := Real.sqrt_nonneg _
    positivity
  nlinarith [norm_nonneg (rho (columnRoot ((b, a))) z - z), hbound, hrhs]

/-! ### Dropping the unit-vector normalization -/

/-- The displacement bound for an arbitrary vector, by homogeneity. -/
theorem norm_columnRoot_displacement_le
    (z : E) (b : Fin 2) (a : FreeAlgebra ℤ X) (delta : ℝ) (hdelta : 0 < delta)
    (hnear : ∀ s ∈ integralControlSet X, ‖rho s z - z‖ < delta) :
    ‖rho (columnRoot ((b, a))) z - z‖ ≤
      13 * (Real.sqrt (Fintype.card X) + 7) * delta := by
  have hCnn : (0 : ℝ) ≤ 13 * (Real.sqrt (Fintype.card X) + 7) := by
    have : (0 : ℝ) ≤ Real.sqrt (Fintype.card X) := Real.sqrt_nonneg _
    positivity
  rcases eq_or_ne z 0 with rfl | hz0
  · simp only [map_zero, sub_zero, norm_zero]
    positivity
  · have hc : 0 < ‖z‖ := norm_pos_iff.mpr hz0
    have hne : ‖z‖ ≠ 0 := ne_of_gt hc
    have hz' : ‖(‖z‖⁻¹ : ℝ) • z‖ = 1 := by
      rw [norm_smul, norm_inv, norm_norm]
      field_simp
    have hsmul : ∀ g : elementaryGroup (Fin 3) (FreeAlgebra ℤ X),
        rho g ((‖z‖⁻¹ : ℝ) • z) - (‖z‖⁻¹ : ℝ) • z =
          (‖z‖⁻¹ : ℝ) • (rho g z - z) := by
      intro g
      rw [map_smul, smul_sub]
    have hnear' : ∀ s ∈ integralControlSet X,
        ‖rho s ((‖z‖⁻¹ : ℝ) • z) - (‖z‖⁻¹ : ℝ) • z‖ < delta / ‖z‖ := by
      intro s hs
      rw [hsmul s, norm_smul, norm_inv, norm_norm, div_eq_inv_mul]
      exact mul_lt_mul_of_pos_left (hnear s hs) (by positivity)
    have hmain := norm_columnRoot_displacement_le_of_unit rho _ hz' b a
      (delta / ‖z‖) (by positivity) hnear'
    rw [hsmul (columnRoot ((b, a))), norm_smul, norm_inv, norm_norm,
      div_eq_inv_mul] at hmain
    have h1 : ‖z‖ * (‖z‖⁻¹ * ‖rho (columnRoot ((b, a))) z - z‖) ≤
        ‖z‖ * (13 * (Real.sqrt (Fintype.card X) + 7) *
          (‖z‖⁻¹ * delta)) := by
      exact mul_le_mul_of_nonneg_left hmain hc.le
    have h2 : ‖z‖ * (‖z‖⁻¹ * ‖rho (columnRoot ((b, a))) z - z‖) =
        ‖rho (columnRoot ((b, a))) z - z‖ := by
      field_simp
    have h3 : ‖z‖ * (13 * (Real.sqrt (Fintype.card X) + 7) *
        (‖z‖⁻¹ * delta)) =
        13 * (Real.sqrt (Fintype.card X) + 7) * delta := by
      field_simp
    linarith

/-! ### The fixed root, by the reindexing symmetry -/

/-- The estimate at the fixed root `(0,1)`, obtained from the column root
`(0,2)` by the transposition of the last two matrix coordinates. -/
theorem integralFixedRootCoefficientDisplacementBound
    (Y : Type u) [Fintype Y] :
    IntegralFixedRootCoefficientDisplacementBound.{u, v} Y
      (13 * (Real.sqrt (Fintype.card Y) + 7)) := by
  intro F _ _ _ sigma z delta hdelta hnear a
  let e : Equiv.Perm (Fin 3) := Equiv.swap 1 2
  let sigma' : elementaryGroup (Fin 3) (FreeAlgebra ℤ Y) →* (F ≃ₗᵢ[ℝ] F) :=
    sigma.comp (elementaryReindexEquiv (R := FreeAlgebra ℤ Y) e).toMonoidHom
  have hnear' : ∀ s ∈ integralControlSet Y, ‖sigma' s z - z‖ < delta := by
    intro s hs
    exact hnear _ (elementaryReindexEquiv_mem_integralControlSet Y e hs)
  have hbound := norm_columnRoot_displacement_le sigma' z 0 a delta hdelta hnear'
  have hmap : elementaryReindexEquiv (R := FreeAlgebra ℤ Y) e
      (columnRoot ((0 : Fin 2), a)) =
      elementaryRoot (0 : Fin 3) 1 (by decide) a := by
    have hroot : columnRoot ((0 : Fin 2), a) =
        elementaryRoot (0 : Fin 3) 2 (by decide) a := rfl
    rw [hroot, elementaryReindexEquiv_elementaryRoot]
    congr 1
  have hrewrite : sigma' (columnRoot ((0 : Fin 2), a)) =
      sigma (elementaryRoot (0 : Fin 3) 1 (by decide) a) := by
    change sigma (elementaryReindexEquiv (R := FreeAlgebra ℤ Y) e
      (columnRoot ((0 : Fin 2), a))) = _
    rw [hmap]
  rw [hrewrite] at hbound
  exact hbound

/-! ### The column-plane mass bound, and the printed theorem -/

/-- The explicit constant of the integral column-plane estimate. -/
def integralColumnPlaneConstant (Y : Type u) [Fintype Y] : ℝ :=
  2 * (13 * (Real.sqrt (Fintype.card Y) + 7))

theorem integralColumnPlaneConstant_nonneg (Y : Type u) [Fintype Y] :
    0 ≤ integralColumnPlaneConstant Y := by
  have : (0 : ℝ) ≤ Real.sqrt (Fintype.card Y) := Real.sqrt_nonneg _
  unfold integralColumnPlaneConstant
  positivity

/-- **The integral column-plane mass bound.**  This is the estimate
`IntegralCharacterMass.ColumnPlaneMassBound` names and that the tree left
open over `ℤ⟨X⟩`. -/
theorem integralColumnPlaneMassBound (Y : Type u) [Fintype Y] :
    ColumnPlaneMassBound.{u, v} (FreeAlgebra ℤ Y) (integralControlSet Y)
      (integralColumnPlaneConstant Y) :=
  columnPlaneMassBound_of_displacementBound
    (columnPlaneDisplacementBound_of_rootCoefficientDisplacementBound
      (rootCoefficientDisplacementBound_of_fixedRootBound Y
        (integralFixedRootCoefficientDisplacementBound.{u, v} Y)))

end

/-- **The remaining analytic family of the integral reduction is proved.** -/
theorem integralFreeColumnPlaneMassBounds :
    IntegralFreeColumnPlaneMassBounds := by
  intro Y _
  exact ⟨integralColumnPlaneConstant Y, integralColumnPlaneConstant_nonneg Y,
    integralColumnPlaneMassBound.{0, 0} Y⟩

/-- **Property `(T)` for every elementary group of rank at least three over
every finitely generated unital ring, in every characteristic.**  This is the
statement Theorem 2 of the manuscript cites from Ershov--Jaikin-Zapirain. -/
theorem finitelyGeneratedRingGeneralRankElementaryPropertyT :
    FinitelyGeneratedRingGeneralRankElementaryPropertyT :=
  printedEJZColumnPlaneReduction integralFreeColumnPlaneMassBounds

end IntegralColumnPlaneClosure
end GroupApproximation

open GroupApproximation

#audit_closed_axioms
  IntegralColumnPlaneClosure.integralFreeColumnPlaneMassBounds
#audit_closed_axioms
  IntegralColumnPlaneClosure.finitelyGeneratedRingGeneralRankElementaryPropertyT
