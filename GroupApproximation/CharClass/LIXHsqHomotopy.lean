import GroupApproximation.CharClass.LIXHsqLinear
import GroupApproximation.CharClass.LIXBundlePair

/-!
# The comparison homotopy of the compatibility square

Lane `lix-hsq`.

`hsq`'s two routes into the local model are, after the second excision is composed away,
relative pullbacks along two continuous maps of pairs out of `lixU`:

* the left one sends `v` to the **section at the chart point** `lixBC ((lixFC).symm v)`;
* the right one sends `v` to the point of the **fibre over the section's zero** whose
  standard-frame coordinate is `v`.

They are equal nowhere: the base coordinate varies on the left and is constant on the
right.  This file joins them by a homotopy through maps of pairs.

## The homotopy

Contract the chart point `q` to the origin along the segment `s · q`, and carry the
section's own block coordinates along:

```text
H (s, v) = ( lixBaseChartFun (s·q) , W(s·q) · (0 ⊕ lixEtaLin (s·q) (chart q)) )
```

The chart's reading `chart q` of the section is **held fixed**; only the point at which the
reconstruction's coefficients are evaluated moves.  At `s = 1` the value is the section
itself (`lixSection_eq_mulVec`); at `s = 0` the base point is the zero and the fibre vector
is `lixKLin` read through the frame (`lixFrame_mulVec_lixKLin`).

The segment stays in the ball because the ball is a metric ball around the origin in chart
coordinates, and the value stays off the zero section because the circle height is negative
throughout — so the southern normal form's coefficient `(1 - t)/2` is positive — and
`lixEtaLin` is injective.

## Main definitions

* `lixQ` — the chart point of a point of `lixU`.
* `lixHomotopyFun` — **the homotopy**.
* `lixFibreMap` — the fibre over the section's zero, in the standard frame.

## Main results

* `lixHomotopy_mapsTo` — it is a homotopy of maps of pairs at every parameter.
* `lixHomotopy_at_one`, `lixHomotopy_at_zero` — its two ends.
-/

noncomputable section

namespace GroupApproximation.CharClass

open scoped Matrix
open Set CategoryTheory
open GroupApproximation.STW59
open GroupApproximation.ThirdParty.HamSandwich.SphereOddDegree

set_option linter.unusedSectionVars false

variable {ℓ : ℕ} {dd : Fin ℓ → ℕ} {G : baseM dd → Matrix (VIdx dd) (VIdx dd) ℂ}

/-! ## 1. The parameter space -/

/-- The parameter space of the comparison homotopy. -/
abbrev lixI : Set ℝ := Set.Icc (0 : ℝ) 1

theorem contractibleSpace_lixI : ContractibleSpace ↥lixI :=
  (convex_Icc (0 : ℝ) 1).contractibleSpace ⟨0, Set.left_mem_Icc.mpr zero_le_one⟩

/-! ## 2. The chart point of a point of the neighbourhood -/

/-- The chart point a point of `lixU` comes from. -/
def lixQ (hGc : Continuous G) (hGu : ∀ m, IsCornerUnitary (Vmat m) (G m))
    (v : ↥(lixU hGc hGu)) : ChartSrc × (∀ j : Fin ℓ, Fin (dd j) → ℂ) :=
  (lixFC dd).symm (v : Fin (lixRank dd) → ℂ)

theorem lixQ_mem (hGc : Continuous G) (hGu : ∀ m, IsCornerUnitary (Vmat m) (G m))
    (v : ↥(lixU hGc hGu)) : lixQ hGc hGu v ∈ lixHsqBall hGc hGu :=
  symm_mem_lixHsqBall hGc hGu v.2

theorem continuous_lixQ (hGc : Continuous G)
    (hGu : ∀ m, IsCornerUnitary (Vmat m) (G m)) :
    Continuous (lixQ hGc hGu) :=
  (lixFC dd).continuousOn_symm.comp_continuous continuous_subtype_val
    (fun v => lixU_subset_target hGc hGu v.2)

/-- **The chart's reading of the section at `lixQ v` is the coordinate change of `v`.**
`lixFullChart` is the product chart followed by `lixCoordEquiv`, so inverting it on the
target leaves exactly the coordinate change. -/
theorem lixProductChart_lixQ (hGc : Continuous G)
    (hGu : ∀ m, IsCornerUnitary (Vmat m) (G m)) (v : ↥(lixU hGc hGu)) :
    lixProductChart dd (lixQ hGc hGu v)
      = (lixCoordEquiv dd).symm (v : Fin (lixRank dd) → ℂ) := by
  have h1 : lixFC dd (lixQ hGc hGu v) = (v : Fin (lixRank dd) → ℂ) :=
    (lixFC dd).right_inv (lixU_subset_target hGc hGu v.2)
  have h2 : lixFC dd (lixQ hGc hGu v)
      = (lixCoordEquiv dd) (lixProductChart dd (lixQ hGc hGu v)) := rfl
  rw [h2] at h1
  rw [← h1, (lixCoordEquiv dd).symm_apply_apply]

/-! ## 3. Continuity of the reconstruction -/

theorem continuous_lixTau : Continuous (lixTau (dd := dd)) := by
  have h : Continuous fun q : ChartSrc × (∀ j : Fin ℓ, Fin (dd j) → ℂ) =>
      circHoriz (circChartFun q.1.2) :=
    isCircleChart_sphereOne.continuous_horiz.comp
      (continuous_circChartFun.comp (continuous_snd.comp continuous_fst))
  show Continuous fun q : ChartSrc × (∀ j : Fin ℓ, Fin (dd j) → ℂ) =>
    (1 + circHoriz (circChartFun q.1.2)) / 2
  exact (continuous_const.add h).div_const 2

theorem continuous_lixEtaLin_pair :
    Continuous (fun p : (ChartSrc × (∀ j : Fin ℓ, Fin (dd j) → ℂ))
        × ((Fin 3 → ℂ) × (∀ j : Fin ℓ, Fin (dd j) → ℂ)) => lixEtaLin p.1 p.2) := by
  refine continuous_pi fun i => ?_
  cases i with
  | inl k =>
      simp only [lixEtaLin_inl]
      exact (continuous_apply k).comp (continuous_fst.comp continuous_snd)
  | inr h =>
      simp only [lixEtaLin_inr]
      refine Continuous.mul (Continuous.mul ?_ ?_) ?_
      · exact Complex.continuous_ofReal.comp
          (continuous_lixChi.comp (continuous_lixTau.comp continuous_fst))
      · exact ((continuous_apply h.1.2).comp
          ((continuous_apply h.1.1).comp (continuous_snd.comp continuous_snd)))
      · exact (CPn.continuous_chartVec h.2).comp
          ((continuous_apply h.1.1).comp (continuous_snd.comp continuous_fst))

/-! ## 4. The homotopy -/

/-- The fibre vector of the homotopy. -/
def lixHomotopyVec (hGc : Continuous G) (hGu : ∀ m, IsCornerUnitary (Vmat m) (G m))
    (s : ℝ) (v : ↥(lixU hGc hGu)) : VIdx dd ⊕ VIdx dd → ℂ :=
  mappingTorus Vmat G circHoriz circHeight (lixBaseChartFun dd (s • lixQ hGc hGu v))
    *ᵥ Sum.elim 0 (lixEtaLin (s • lixQ hGc hGu v) (lixProductChart dd (lixQ hGc hGu v)))

theorem lixHomotopyVec_mem (hGc : Continuous G)
    (hGu : ∀ m, IsCornerUnitary (Vmat m) (G m)) (s : ℝ) (v : ↥(lixU hGc hGu)) :
    ((lixBaseChartFun dd (s • lixQ hGc hGu v), lixHomotopyVec hGc hGu s v) :
        (↥sphereOne × baseM dd) × (VIdx dd ⊕ VIdx dd → ℂ))
      ∈ Bundle.totalSet (lixBundle G hGc hGu) :=
  Bundle.mulVec_mulVec_self (lixBundle G hGc hGu) _ _

/-- **The comparison homotopy.** -/
def lixHomotopyFun (hGc : Continuous G) (hGu : ∀ m, IsCornerUnitary (Vmat m) (G m)) :
    C(↥lixI × ↥(lixU hGc hGu), Bundle.Total (lixBundle G hGc hGu)) where
  toFun p := ⟨(lixBaseChartFun dd ((p.1 : ℝ) • lixQ hGc hGu p.2),
    lixHomotopyVec hGc hGu (p.1 : ℝ) p.2), lixHomotopyVec_mem hGc hGu _ _⟩
  continuous_toFun := by
    have hsmul : Continuous fun p : ↥lixI × ↥(lixU hGc hGu) =>
        (p.1 : ℝ) • lixQ hGc hGu p.2 :=
      (continuous_subtype_val.comp continuous_fst).smul
        ((continuous_lixQ hGc hGu).comp continuous_snd)
    have hchart : Continuous fun p : ↥lixI × ↥(lixU hGc hGu) =>
        lixProductChart dd (lixQ hGc hGu p.2) := by
      have h : (fun p : ↥lixI × ↥(lixU hGc hGu) => lixProductChart dd (lixQ hGc hGu p.2))
          = fun p => (lixCoordEquiv dd).symm ((p.2 : Fin (lixRank dd) → ℂ)) :=
        funext fun p => lixProductChart_lixQ hGc hGu p.2
      rw [h]
      exact (lixCoordEquiv dd).symm.continuous.comp
        (continuous_subtype_val.comp continuous_snd)
    have hEta : Continuous fun p : ↥lixI × ↥(lixU hGc hGu) =>
        lixEtaLin ((p.1 : ℝ) • lixQ hGc hGu p.2)
          (lixProductChart dd (lixQ hGc hGu p.2)) :=
      continuous_lixEtaLin_pair.comp (hsmul.prodMk hchart)
    refine Continuous.subtype_mk (Continuous.prodMk
      (continuous_lixBaseChartFun.comp hsmul) ?_) _
    exact ((continuous_mappingTorus_lix hGc).comp
      (continuous_lixBaseChartFun.comp hsmul)).matrix_mulVec
      (continuous_sumElim_right hEta)

/-! ## 5. It is a homotopy of maps of pairs -/

theorem lixHomotopyVec_ne_zero (hGc : Continuous G)
    (hGu : ∀ m, IsCornerUnitary (Vmat m) (G m)) {s : ℝ} (hs : s ∈ lixI)
    {v : ↥(lixU hGc hGu)} (hv : (v : Fin (lixRank dd) → ℂ) ≠ 0) :
    lixHomotopyVec hGc hGu s v ≠ 0 := by
  intro hzero
  have hqmem : s • lixQ hGc hGu v ∈ lixHsqBall hGc hGu :=
    smul_mem_lixHsqBall hGc hGu (lixQ_mem hGc hGu v) hs
  have hu : (s • lixQ hGc hGu v).1.2 ∈ Ioo (-1 : ℝ) 1 :=
    circCoord_mem_Ioo_of_mem_lixHsqBall hGc hGu hqmem
  have hw : Vmat (lixBaseChartFun dd (s • lixQ hGc hGu v)).2
        *ᵥ lixEtaLin (s • lixQ hGc hGu v) (lixProductChart dd (lixQ hGc hGu v))
      = lixEtaLin (s • lixQ hGc hGu v) (lixProductChart dd (lixQ hGc hGu v)) :=
    Vmat_mulVec_lixEtaLin _ _
  have hform := mtSection_south_form' (V := Vmat) (G := G) (y := circHoriz)
    (t := circHeight)
    (η := fun _ => lixEtaLin (s • lixQ hGc hGu v) (lixProductChart dd (lixQ hGc hGu v)))
    (p := lixBaseChartFun dd (s • lixQ hGc hGu v)) hw
  rw [lixHomotopyVec, hform] at hzero
  have hsecond := (sumElim_eq_zero_iff.mp hzero).2
  have hneg : circHeight (lixBaseChartFun dd (s • lixQ hGc hGu v)).1 < 0 :=
    circHeight_circChartFun_neg hu
  have hcoef : ((((1 - circHeight (lixBaseChartFun dd (s • lixQ hGc hGu v)).1) / 2 : ℝ))
      : ℂ) ≠ 0 := by
    have : (0 : ℝ) < (1 - circHeight (lixBaseChartFun dd (s • lixQ hGc hGu v)).1) / 2 := by
      linarith
    exact_mod_cast this.ne'
  have hetaz : lixEtaLin (s • lixQ hGc hGu v) (lixProductChart dd (lixQ hGc hGu v)) = 0 :=
    (smul_eq_zero.mp hsecond).resolve_left hcoef
  have hab : lixProductChart dd (lixQ hGc hGu v) = 0 :=
    (lixEtaLin_eq_zero_iff hu _).mp hetaz
  rw [lixProductChart_lixQ hGc hGu v] at hab
  exact hv (by
    have := congrArg (fun x => (lixCoordEquiv dd) x) hab
    rwa [(lixCoordEquiv dd).apply_symm_apply, map_zero] at this)

theorem lixHomotopy_mapsTo (hGc : Continuous G)
    (hGu : ∀ m, IsCornerUnitary (Vmat m) (G m)) :
    ∀ p ∈ {p : ↥lixI × ↥(lixU hGc hGu) |
        p.2 ∈ ((Subtype.val : ↥(lixU hGc hGu) → (Fin (lixRank dd) → ℂ)) ⁻¹'
          ({0}ᶜ : Set (Fin (lixRank dd) → ℂ)))},
      (ConcreteCategory.hom (cmap (lixHomotopyFun hGc hGu))) p
        ∈ lixPuncturedInTotal hGc hGu := by
  intro p hp
  exact ⟨lixHomotopyVec_mem hGc hGu _ _,
    lixHomotopyVec_ne_zero hGc hGu p.1.2 hp⟩

/-! ## 6. The two ends -/

theorem lixFibre_mem (hGc : Continuous G) (hGu : ∀ m, IsCornerUnitary (Vmat m) (G m))
    (y : Fin (lixRank dd) → ℂ) :
    ((lixZero dd, lixFrame hGc hGu *ᵥ y) :
        (↥sphereOne × baseM dd) × (VIdx dd ⊕ VIdx dd → ℂ))
      ∈ Bundle.totalSet (lixBundle G hGc hGu) := by
  show mappingTorus Vmat G circHoriz circHeight (lixZero dd) *ᵥ (lixFrame hGc hGu *ᵥ y)
    = lixFrame hGc hGu *ᵥ y
  rw [Matrix.mulVec_mulVec, ← lixFrame_mul_conjTranspose hGc hGu, Matrix.mul_assoc,
    lixFrame_conjTranspose_mul, Matrix.mul_one]

/-- **The fibre over the section's zero, in the standard frame.** -/
def lixFibreMap (hGc : Continuous G) (hGu : ∀ m, IsCornerUnitary (Vmat m) (G m)) :
    C(Fin (lixRank dd) → ℂ, Bundle.Total (lixBundle G hGc hGu)) where
  toFun y := ⟨(lixZero dd, lixFrame hGc hGu *ᵥ y), lixFibre_mem hGc hGu y⟩
  continuous_toFun :=
    (continuous_const.prodMk (continuous_const.matrix_mulVec continuous_id)).subtype_mk _

/-- **The near end is the section at the chart point.** -/
theorem lixHomotopy_at_one (hGc : Continuous G)
    (hGu : ∀ m, IsCornerUnitary (Vmat m) (G m))
    (hGe : ∀ m, G m *ᵥ Sum.elim (aVec m) 0 = Sum.elim (bVec m) 0)
    (v : ↥(lixU hGc hGu)) :
    lixHomotopyFun hGc hGu (⟨(1 : ℝ), Set.right_mem_Icc.mpr zero_le_one⟩, v)
      = lixSectionTotal hGc hGu hGe (lixBaseChartFun dd (lixQ hGc hGu v)) := by
  have hu : (lixQ hGc hGu v).1.2 ∈ Ioo (-1 : ℝ) 1 :=
    circCoord_mem_Ioo_of_mem_lixHsqBall hGc hGu (lixQ_mem hGc hGu v)
  have hsq : sphereQ (lixQ hGc hGu v).1.1 ≤ 1 :=
    sphereQ_le_one_of_mem_lixHsqBall hGc hGu (lixQ_mem hGc hGu v)
  refine Subtype.ext (Prod.ext ?_ ?_)
  · show lixBaseChartFun dd ((1 : ℝ) • lixQ hGc hGu v) = lixBaseChartFun dd (lixQ hGc hGu v)
    rw [one_smul]
  · show lixHomotopyVec hGc hGu 1 v = lixSection G (lixBaseChartFun dd (lixQ hGc hGu v))
    rw [lixHomotopyVec, one_smul]
    exact (lixSection_eq_mulVec (G := G) hu hsq).symm

/-- **The far end is the frame applied to `lixKLin`.** -/
theorem lixHomotopy_at_zero (hGc : Continuous G)
    (hGu : ∀ m, IsCornerUnitary (Vmat m) (G m)) (v : ↥(lixU hGc hGu)) :
    lixHomotopyFun hGc hGu (⟨(0 : ℝ), Set.left_mem_Icc.mpr zero_le_one⟩, v)
      = lixFibreMap hGc hGu (lixKLin hGc hGu (v : Fin (lixRank dd) → ℂ)) := by
  refine Subtype.ext (Prod.ext ?_ ?_)
  · show lixBaseChartFun dd ((0 : ℝ) • lixQ hGc hGu v) = lixZero dd
    rw [zero_smul]
    exact lixBaseChartFun_zero
  · show lixHomotopyVec hGc hGu 0 v
      = lixFrame hGc hGu *ᵥ lixKLin hGc hGu (v : Fin (lixRank dd) → ℂ)
    rw [lixFrame_mulVec_lixKLin, lixHomotopyVec, zero_smul,
      lixProductChart_lixQ hGc hGu v, lixBaseChartFun_zero]
    rfl

/-! Printed on every build. -/

#print axioms lixHomotopy_mapsTo

end GroupApproximation.CharClass
