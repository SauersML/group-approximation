import GroupApproximation.CharClass.LIXKGenLocalLinear
import GroupApproximation.CharClass.LIXKGenLocalNbhd
import GroupApproximation.CharClass.LIXHsqHomotopy
import GroupApproximation.CharClass.BundleTotalOver
import GroupApproximation.Meta.AxiomGuard

/-!
# The comparison homotopy at the `i`-th zero, and the legs of the local square, at rank `n`

Lane `lx-local2a` of the LIX strongest swarm (the rank-`n`, `k`-zero port of
`CharClass/LIXHsqHomotopy.lean` and of the maps of `CharClass/LIXHsqLegs.lean`).

The local computation `KGen.KGenLocalNonzero` compares two maps of pairs out of the
neighbourhood `lixKU n k dd i` of the origin of the local model:

* the left leg sends `v` to the **section at the chart point** `lixKBC ((lixKFC).symm v)`, a
  point of the neighbourhood `lixKTrivBall n k dd i` of the `i`-th zero, which contains no other
  zero;
* the right leg sends `v` to the point of the **fibre over the `i`-th zero** whose standard-frame
  coordinate is `v`.

This file builds the maps and the homotopy joining them, and nothing cohomological: every map
here is a map of spaces or of pairs, with no coefficient ring anywhere, so the relative-pullback
arguments over `ZMod 2` and over a field both consume it.

## The homotopy

Contract the chart point `q` to the origin along `s · q`, holding the chart's reading of the
section fixed:

```text
H (s, v) = ( lixKBaseChart (s·q) , W(s·q) · (0 ⊕ lixKEtaLin (s·q) (lixKProductChart q)) )
```

At `s = 1` it is the section at the chart point (`lixKSection_eq_mulVec`); at `s = 0` the base
point is the `i`-th zero and the fibre vector is the frame applied to `lixKGLin`
(`lixKGFrame_mulVec_lixKGLin`).  The segment stays in the ball `lixKHsqBall` (star-shaped), where
both clamps are inactive, and the value stays off the zero section because the circle height is
negative there and `lixKEtaLin` is injective.

The left leg lands in the pair `(lixKTrivBall, lixKTrivBall ∖ Z)` over the whole zero set `Z`,
which is the target of `LIXKRelMV.restrictTo`: a chart point is not the `i`-th zero unless `v = 0`
(the chart is injective on its source), and it is no other zero because the neighbourhood holds
none.  No excision is used.

## Main definitions

* `KGen.lixKQ` — the chart point of a point of `lixKU`.
* `KGen.lixKHomotopyFun` — **the homotopy**; `KGen.lixKFibreMap` — the fibre over the `i`-th zero.
* `KGen.lixKChartPt`, `lixKGLmap` — the left leg; `lixKIncF`, `lixKTrivInv`, `lixKInclOn`,
  `lixKGRmap`, `lixKGRmap'`, `lixKFarMap` — the right leg and the forms it passes through.

## Main results

* `KGen.lixKHomotopy_mapsTo` — a homotopy of maps of pairs at every parameter.
* `KGen.lixKHomotopy_at_one`, `lixKHomotopy_at_zero` — its ends.
* `KGen.lixKChartPt_mapsTo` — the chart point misses the zero set off the origin.
* `KGen.lixKGRmap_eq` — the right leg is the fibre map.
* `KGen.lixKHomotopy_end_one`, `lixKHomotopy_end_zero` — the ends as the two legs.
-/

noncomputable section

namespace GroupApproximation.CharClass

namespace KGen

open scoped Matrix
open Set CategoryTheory
open GroupApproximation.STW59
open GroupApproximation.ThirdParty.HamSandwich.SphereOddDegree

set_option linter.unusedSectionVars false

variable {ℓ : ℕ}

/-! ## 1. The chart point of a point of the neighbourhood -/

/-- The restricted base chart agrees with the base chart. -/
@[simp] theorem lixKBC_apply (n k : ℕ) (dd : Fin ℓ → ℕ) (i : Fin (k + 1))
    (q : ChartSrc n × (∀ j : Fin ℓ, Fin (dd j) → ℂ)) :
    lixKBC n k dd i q = lixKBaseChart n k dd i q := rfl

theorem lixKHsqBall_subset_baseChart_source (n k : ℕ) (dd : Fin ℓ → ℕ) (i : Fin (k + 1))
    {G : Gen.baseM n dd → Matrix (Gen.VIdx n dd) (Gen.VIdx n dd) ℂ}
    (hGc : Continuous G) (hGu : ∀ m, IsCornerUnitary (Gen.Vmat n m) (G m)) :
    lixKHsqBall n k dd i hGc hGu ⊆ (lixKBaseChart n k dd i).source := by
  intro q hq
  have h := lixKHsqBall_subset_bc_source n k dd i hGc hGu hq
  rw [lixKBC, OpenPartialHomeomorph.restrOpen_source] at h
  exact h.1

/-- The chart point a point of `lixKU` comes from. -/
def lixKQ (n k : ℕ) (dd : Fin ℓ → ℕ) (i : Fin (k + 1))
    {G : Gen.baseM n dd → Matrix (Gen.VIdx n dd) (Gen.VIdx n dd) ℂ}
    (hGc : Continuous G) (hGu : ∀ m, IsCornerUnitary (Gen.Vmat n m) (G m))
    (v : ↥(lixKU n k dd i hGc hGu)) : ChartSrc n × (∀ j : Fin ℓ, Fin (dd j) → ℂ) :=
  (lixKFC n k dd i).symm (v : Fin (lixRank n dd) → ℂ)

theorem lixKQ_mem (n k : ℕ) (dd : Fin ℓ → ℕ) (i : Fin (k + 1))
    {G : Gen.baseM n dd → Matrix (Gen.VIdx n dd) (Gen.VIdx n dd) ℂ}
    (hGc : Continuous G) (hGu : ∀ m, IsCornerUnitary (Gen.Vmat n m) (G m))
    (v : ↥(lixKU n k dd i hGc hGu)) :
    lixKQ n k dd i hGc hGu v ∈ lixKHsqBall n k dd i hGc hGu :=
  symm_mem_lixKHsqBall n k dd i hGc hGu v.2

theorem continuous_lixKQ (n k : ℕ) (dd : Fin ℓ → ℕ) (i : Fin (k + 1))
    {G : Gen.baseM n dd → Matrix (Gen.VIdx n dd) (Gen.VIdx n dd) ℂ}
    (hGc : Continuous G) (hGu : ∀ m, IsCornerUnitary (Gen.Vmat n m) (G m)) :
    Continuous (lixKQ n k dd i hGc hGu) :=
  (lixKFC n k dd i).continuousOn_symm.comp_continuous continuous_subtype_val
    (fun v => lixKU_subset_target n k dd i hGc hGu v.2)

/-- **The chart's reading of the section at `lixKQ v` is the coordinate change of `v`.** -/
theorem lixKProductChart_lixKQ (n k : ℕ) (dd : Fin ℓ → ℕ) (i : Fin (k + 1))
    {G : Gen.baseM n dd → Matrix (Gen.VIdx n dd) (Gen.VIdx n dd) ℂ}
    (hGc : Continuous G) (hGu : ∀ m, IsCornerUnitary (Gen.Vmat n m) (G m))
    (v : ↥(lixKU n k dd i hGc hGu)) :
    lixKProductChart n dd (lixKQ n k dd i hGc hGu v)
      = (lixKCoordEquiv n dd).symm (v : Fin (lixRank n dd) → ℂ) := by
  have h1 : lixKFC n k dd i (lixKQ n k dd i hGc hGu v) = (v : Fin (lixRank n dd) → ℂ) :=
    (lixKFC n k dd i).right_inv (lixKU_subset_target n k dd i hGc hGu v.2)
  have h2 : lixKFC n k dd i (lixKQ n k dd i hGc hGu v)
      = (lixKCoordEquiv n dd) (lixKProductChart n dd (lixKQ n k dd i hGc hGu v)) := rfl
  rw [h2] at h1
  rw [← h1, (lixKCoordEquiv n dd).symm_apply_apply]

/-! ## 2. Continuity of the reconstruction -/

theorem continuous_lixKTau (n : ℕ) (dd : Fin ℓ → ℕ) : Continuous (lixKTau (dd := dd) n) := by
  have h : Continuous fun q : ChartSrc n × (∀ j : Fin ℓ, Fin (dd j) → ℂ) =>
      circHoriz (circChartFun q.1.2) :=
    isCircleChart_sphereOne.continuous_horiz.comp
      (continuous_circChartFun.comp (continuous_snd.comp continuous_fst))
  show Continuous fun q : ChartSrc n × (∀ j : Fin ℓ, Fin (dd j) → ℂ) =>
    (1 + circHoriz (circChartFun q.1.2)) / 2
  exact (continuous_const.add h).div_const 2

theorem continuous_lixKEtaLin_pair (n : ℕ) (dd : Fin ℓ → ℕ) :
    Continuous (fun p : (ChartSrc n × (∀ j : Fin ℓ, Fin (dd j) → ℂ))
        × ((Fin (n + 1) → ℂ) × (∀ j : Fin ℓ, Fin (dd j) → ℂ)) => lixKEtaLin n p.1 p.2) := by
  refine continuous_pi fun x => ?_
  cases x with
  | inl a =>
      simp only [lixKEtaLin_inl]
      exact (continuous_apply a).comp (continuous_fst.comp continuous_snd)
  | inr h =>
      simp only [lixKEtaLin_inr]
      refine Continuous.mul (Continuous.mul ?_ ?_) ?_
      · exact Complex.continuous_ofReal.comp
          (continuous_lixChi.comp ((continuous_lixKTau n dd).comp continuous_fst))
      · exact ((continuous_apply h.1.2).comp
          ((continuous_apply h.1.1).comp (continuous_snd.comp continuous_snd)))
      · exact (CPn.continuous_chartVec h.2).comp
          ((continuous_apply h.1.1).comp (continuous_snd.comp continuous_fst))

theorem continuous_lixKHomotopySmul (n k : ℕ) (dd : Fin ℓ → ℕ) (i : Fin (k + 1))
    {G : Gen.baseM n dd → Matrix (Gen.VIdx n dd) (Gen.VIdx n dd) ℂ}
    (hGc : Continuous G) (hGu : ∀ m, IsCornerUnitary (Gen.Vmat n m) (G m)) :
    Continuous fun p : ↥lixI × ↥(lixKU n k dd i hGc hGu) =>
      (p.1 : ℝ) • lixKQ n k dd i hGc hGu p.2 :=
  (continuous_subtype_val.comp continuous_fst).smul
    ((continuous_lixKQ n k dd i hGc hGu).comp continuous_snd)

theorem lixKHomotopySmul_mem (n k : ℕ) (dd : Fin ℓ → ℕ) (i : Fin (k + 1))
    {G : Gen.baseM n dd → Matrix (Gen.VIdx n dd) (Gen.VIdx n dd) ℂ}
    (hGc : Continuous G) (hGu : ∀ m, IsCornerUnitary (Gen.Vmat n m) (G m))
    (p : ↥lixI × ↥(lixKU n k dd i hGc hGu)) :
    (p.1 : ℝ) • lixKQ n k dd i hGc hGu p.2 ∈ lixKHsqBall n k dd i hGc hGu :=
  smul_mem_lixKHsqBall n k dd i hGc hGu (lixKQ_mem n k dd i hGc hGu p.2) p.1.2

theorem continuous_lixKHomotopyBase (n k : ℕ) (dd : Fin ℓ → ℕ) (i : Fin (k + 1))
    {G : Gen.baseM n dd → Matrix (Gen.VIdx n dd) (Gen.VIdx n dd) ℂ}
    (hGc : Continuous G) (hGu : ∀ m, IsCornerUnitary (Gen.Vmat n m) (G m)) :
    Continuous fun p : ↥lixI × ↥(lixKU n k dd i hGc hGu) =>
      lixKBaseChart n k dd i ((p.1 : ℝ) • lixKQ n k dd i hGc hGu p.2) :=
  (lixKBaseChart n k dd i).continuousOn.comp_continuous
    (continuous_lixKHomotopySmul n k dd i hGc hGu)
    (fun p => lixKHsqBall_subset_baseChart_source n k dd i hGc hGu
      (lixKHomotopySmul_mem n k dd i hGc hGu p))

/-! ## 3. The homotopy -/

/-- The fibre vector of the homotopy. -/
def lixKHomotopyVec (n k : ℕ) (dd : Fin ℓ → ℕ) (i : Fin (k + 1))
    {G : Gen.baseM n dd → Matrix (Gen.VIdx n dd) (Gen.VIdx n dd) ℂ}
    (hGc : Continuous G) (hGu : ∀ m, IsCornerUnitary (Gen.Vmat n m) (G m))
    (s : ℝ) (v : ↥(lixKU n k dd i hGc hGu)) : Gen.VIdx n dd ⊕ Gen.VIdx n dd → ℂ :=
  mappingTorus (Gen.Vmat n) G circHoriz circHeight
      (lixKBaseChart n k dd i (s • lixKQ n k dd i hGc hGu v))
    *ᵥ Sum.elim 0 (lixKEtaLin n (s • lixKQ n k dd i hGc hGu v)
      (lixKProductChart n dd (lixKQ n k dd i hGc hGu v)))

theorem lixKHomotopyVec_mem (n k : ℕ) (dd : Fin ℓ → ℕ) (i : Fin (k + 1))
    {G : Gen.baseM n dd → Matrix (Gen.VIdx n dd) (Gen.VIdx n dd) ℂ}
    (hGc : Continuous G) (hGu : ∀ m, IsCornerUnitary (Gen.Vmat n m) (G m))
    (s : ℝ) (v : ↥(lixKU n k dd i hGc hGu)) :
    ((lixKBaseChart n k dd i (s • lixKQ n k dd i hGc hGu v),
        lixKHomotopyVec n k dd i hGc hGu s v) :
        (↥sphereOne × Gen.baseM n dd) × (Gen.VIdx n dd ⊕ Gen.VIdx n dd → ℂ))
      ∈ Bundle.totalSet (lixBundle n G hGc hGu) :=
  Bundle.mulVec_mulVec_self (lixBundle n G hGc hGu) _ _

/-- **The comparison homotopy at the `i`-th zero.** -/
def lixKHomotopyFun (n k : ℕ) (dd : Fin ℓ → ℕ) (i : Fin (k + 1))
    {G : Gen.baseM n dd → Matrix (Gen.VIdx n dd) (Gen.VIdx n dd) ℂ}
    (hGc : Continuous G) (hGu : ∀ m, IsCornerUnitary (Gen.Vmat n m) (G m)) :
    C(↥lixI × ↥(lixKU n k dd i hGc hGu), Bundle.Total (lixBundle n G hGc hGu)) where
  toFun p := ⟨(lixKBaseChart n k dd i ((p.1 : ℝ) • lixKQ n k dd i hGc hGu p.2),
    lixKHomotopyVec n k dd i hGc hGu (p.1 : ℝ) p.2), lixKHomotopyVec_mem n k dd i hGc hGu _ _⟩
  continuous_toFun := by
    have hchart : Continuous fun p : ↥lixI × ↥(lixKU n k dd i hGc hGu) =>
        lixKProductChart n dd (lixKQ n k dd i hGc hGu p.2) := by
      have h : (fun p : ↥lixI × ↥(lixKU n k dd i hGc hGu) =>
          lixKProductChart n dd (lixKQ n k dd i hGc hGu p.2))
          = fun p => (lixKCoordEquiv n dd).symm ((p.2 : Fin (lixRank n dd) → ℂ)) :=
        funext fun p => lixKProductChart_lixKQ n k dd i hGc hGu p.2
      rw [h]
      exact (lixKCoordEquiv n dd).symm.continuous.comp
        (continuous_subtype_val.comp continuous_snd)
    have hEta : Continuous fun p : ↥lixI × ↥(lixKU n k dd i hGc hGu) =>
        lixKEtaLin n ((p.1 : ℝ) • lixKQ n k dd i hGc hGu p.2)
          (lixKProductChart n dd (lixKQ n k dd i hGc hGu p.2)) :=
      (continuous_lixKEtaLin_pair n dd).comp
        ((continuous_lixKHomotopySmul n k dd i hGc hGu).prodMk hchart)
    refine Continuous.subtype_mk (Continuous.prodMk
      (continuous_lixKHomotopyBase n k dd i hGc hGu) ?_) _
    exact ((continuous_mappingTorus_lix n hGc).comp
      (continuous_lixKHomotopyBase n k dd i hGc hGu)).matrix_mulVec
      (continuous_sumElim_right hEta)

/-! ## 4. It is a homotopy of maps of pairs -/

theorem lixKHomotopyVec_ne_zero (n k : ℕ) (dd : Fin ℓ → ℕ) (i : Fin (k + 1))
    {G : Gen.baseM n dd → Matrix (Gen.VIdx n dd) (Gen.VIdx n dd) ℂ}
    (hGc : Continuous G) (hGu : ∀ m, IsCornerUnitary (Gen.Vmat n m) (G m))
    {s : ℝ} (hs : s ∈ lixI) {v : ↥(lixKU n k dd i hGc hGu)}
    (hv : (v : Fin (lixRank n dd) → ℂ) ≠ 0) :
    lixKHomotopyVec n k dd i hGc hGu s v ≠ 0 := by
  intro hzero
  have hqmem : s • lixKQ n k dd i hGc hGu v ∈ lixKHsqBall n k dd i hGc hGu :=
    smul_mem_lixKHsqBall n k dd i hGc hGu (lixKQ_mem n k dd i hGc hGu v) hs
  have hu : (s • lixKQ n k dd i hGc hGu v).1.2 ∈ Ioo (-1 : ℝ) 1 :=
    circCoord_mem_Ioo_of_mem_lixKHsqBall n k dd i hGc hGu hqmem
  have hw : Gen.Vmat n (lixKBaseChart n k dd i (s • lixKQ n k dd i hGc hGu v)).2
        *ᵥ lixKEtaLin n (s • lixKQ n k dd i hGc hGu v)
          (lixKProductChart n dd (lixKQ n k dd i hGc hGu v))
      = lixKEtaLin n (s • lixKQ n k dd i hGc hGu v)
          (lixKProductChart n dd (lixKQ n k dd i hGc hGu v)) :=
    Vmat_mulVec_lixKEtaLin n k i _ _
  have hform := mtSection_south_form' (V := Gen.Vmat n) (G := G) (y := circHoriz)
    (t := circHeight)
    (η := fun _ => lixKEtaLin n (s • lixKQ n k dd i hGc hGu v)
      (lixKProductChart n dd (lixKQ n k dd i hGc hGu v)))
    (p := lixKBaseChart n k dd i (s • lixKQ n k dd i hGc hGu v)) hw
  rw [lixKHomotopyVec, hform] at hzero
  have hsecond := (sumElim_eq_zero_iff.mp hzero).2
  have hneg : circHeight (lixKBaseChart n k dd i (s • lixKQ n k dd i hGc hGu v)).1 < 0 :=
    circHeight_circChartFun_neg hu
  have hcoef : ((((1 - circHeight
      (lixKBaseChart n k dd i (s • lixKQ n k dd i hGc hGu v)).1) / 2 : ℝ)) : ℂ) ≠ 0 := by
    have : (0 : ℝ) < (1 - circHeight
        (lixKBaseChart n k dd i (s • lixKQ n k dd i hGc hGu v)).1) / 2 := by
      linarith
    exact_mod_cast this.ne'
  have hetaz : lixKEtaLin n (s • lixKQ n k dd i hGc hGu v)
      (lixKProductChart n dd (lixKQ n k dd i hGc hGu v)) = 0 :=
    (smul_eq_zero.mp hsecond).resolve_left hcoef
  have hab : lixKProductChart n dd (lixKQ n k dd i hGc hGu v) = 0 :=
    (lixKEtaLin_eq_zero_iff n hu _).mp hetaz
  rw [lixKProductChart_lixKQ n k dd i hGc hGu v] at hab
  exact hv (by
    have := congrArg (fun x => (lixKCoordEquiv n dd) x) hab
    rwa [(lixKCoordEquiv n dd).apply_symm_apply, map_zero] at this)

/-- **The homotopy is a homotopy of maps of pairs**, at every parameter. -/
theorem lixKHomotopy_mapsTo (n k : ℕ) (dd : Fin ℓ → ℕ) (i : Fin (k + 1))
    {G : Gen.baseM n dd → Matrix (Gen.VIdx n dd) (Gen.VIdx n dd) ℂ}
    (hGc : Continuous G) (hGu : ∀ m, IsCornerUnitary (Gen.Vmat n m) (G m)) :
    ∀ p ∈ {p : ↥lixI × ↥(lixKU n k dd i hGc hGu) |
        p.2 ∈ ((Subtype.val : ↥(lixKU n k dd i hGc hGu) → (Fin (lixRank n dd) → ℂ)) ⁻¹'
          ({0}ᶜ : Set (Fin (lixRank n dd) → ℂ)))},
      (ConcreteCategory.hom (cmap (lixKHomotopyFun n k dd i hGc hGu))) p
        ∈ lixPuncturedInTotal n hGc hGu := by
  intro p hp
  exact ⟨lixKHomotopyVec_mem n k dd i hGc hGu _ _,
    lixKHomotopyVec_ne_zero n k dd i hGc hGu p.1.2 hp⟩

/-! ## 5. The fibre over the `i`-th zero, and the two ends -/

theorem lixKFibre_mem (n k : ℕ) (dd : Fin ℓ → ℕ) (i : Fin (k + 1))
    {G : Gen.baseM n dd → Matrix (Gen.VIdx n dd) (Gen.VIdx n dd) ℂ}
    (hGc : Continuous G) (hGu : ∀ m, IsCornerUnitary (Gen.Vmat n m) (G m))
    (y : Fin (lixRank n dd) → ℂ) :
    ((lixKZero n k dd i, lixKGFrame n k i hGc hGu *ᵥ y) :
        (↥sphereOne × Gen.baseM n dd) × (Gen.VIdx n dd ⊕ Gen.VIdx n dd → ℂ))
      ∈ Bundle.totalSet (lixBundle n G hGc hGu) := by
  show mappingTorus (Gen.Vmat n) G circHoriz circHeight (lixKZero n k dd i)
      *ᵥ (lixKGFrame n k i hGc hGu *ᵥ y) = lixKGFrame n k i hGc hGu *ᵥ y
  rw [Matrix.mulVec_mulVec, ← lixKGFrame_mul_conjTranspose n k i hGc hGu, Matrix.mul_assoc,
    lixKGFrame_conjTranspose_mul, Matrix.mul_one]

/-- **The fibre over the `i`-th zero, in its standard frame.** -/
def lixKFibreMap (n k : ℕ) (dd : Fin ℓ → ℕ) (i : Fin (k + 1))
    {G : Gen.baseM n dd → Matrix (Gen.VIdx n dd) (Gen.VIdx n dd) ℂ}
    (hGc : Continuous G) (hGu : ∀ m, IsCornerUnitary (Gen.Vmat n m) (G m)) :
    C(Fin (lixRank n dd) → ℂ, Bundle.Total (lixBundle n G hGc hGu)) where
  toFun y := ⟨(lixKZero n k dd i, lixKGFrame n k i hGc hGu *ᵥ y),
    lixKFibre_mem n k dd i hGc hGu y⟩
  continuous_toFun :=
    (continuous_const.prodMk (continuous_const.matrix_mulVec continuous_id)).subtype_mk _

theorem lixKFibreMap_mapsTo (n k : ℕ) (dd : Fin ℓ → ℕ) (i : Fin (k + 1))
    {G : Gen.baseM n dd → Matrix (Gen.VIdx n dd) (Gen.VIdx n dd) ℂ}
    (hGc : Continuous G) (hGu : ∀ m, IsCornerUnitary (Gen.Vmat n m) (G m)) :
    ∀ y ∈ puncturedSet (lixRank n dd),
      (ConcreteCategory.hom (cmap (lixKFibreMap n k dd i hGc hGu))) y
        ∈ lixPuncturedInTotal n hGc hGu := by
  intro y hy
  refine ⟨lixKFibre_mem n k dd i hGc hGu y, ?_⟩
  intro hzero
  refine hy ?_
  have h2 : (lixKGFrame n k i hGc hGu)ᴴ *ᵥ (lixKGFrame n k i hGc hGu *ᵥ y) = y := by
    rw [Matrix.mulVec_mulVec, lixKGFrame_conjTranspose_mul, Matrix.one_mulVec]
  have h3 : lixKGFrame n k i hGc hGu *ᵥ y = 0 := hzero
  rw [h3, Matrix.mulVec_zero] at h2
  exact h2.symm

/-- **The near end is the section at the chart point.** -/
theorem lixKHomotopy_at_one (n k : ℕ) (dd : Fin ℓ → ℕ) (i : Fin (k + 1))
    {G : Gen.baseM n dd → Matrix (Gen.VIdx n dd) (Gen.VIdx n dd) ℂ}
    (hGc : Continuous G) (hGu : ∀ m, IsCornerUnitary (Gen.Vmat n m) (G m))
    (hGe : ∀ m, G m *ᵥ Sum.elim (aVecK n m) 0 = Sum.elim (bVecK n k m) 0)
    (v : ↥(lixKU n k dd i hGc hGu)) :
    lixKHomotopyFun n k dd i hGc hGu (⟨(1 : ℝ), Set.right_mem_Icc.mpr zero_le_one⟩, v)
      = lixKSectionTotal n k hGc hGu hGe (lixKBC n k dd i (lixKQ n k dd i hGc hGu v)) := by
  have hu : (lixKQ n k dd i hGc hGu v).1.2 ∈ Ioo (-1 : ℝ) 1 :=
    circCoord_mem_Ioo_of_mem_lixKHsqBall n k dd i hGc hGu (lixKQ_mem n k dd i hGc hGu v)
  have hsq : chartQ n (lixKQ n k dd i hGc hGu v).1.1 ≤ 1 :=
    chartQ_le_one_of_mem_lixKHsqBall n k dd i hGc hGu (lixKQ_mem n k dd i hGc hGu v)
  rw [lixKBC_apply]
  refine Subtype.ext (Prod.ext ?_ ?_)
  · show lixKBaseChart n k dd i ((1 : ℝ) • lixKQ n k dd i hGc hGu v)
      = lixKBaseChart n k dd i (lixKQ n k dd i hGc hGu v)
    rw [one_smul]
  · show lixKHomotopyVec n k dd i hGc hGu 1 v
      = lixKSection n k G (lixKBaseChart n k dd i (lixKQ n k dd i hGc hGu v))
    rw [lixKHomotopyVec, one_smul]
    exact (lixKSection_eq_mulVec n k i (G := G) hu hsq).symm

/-- **The far end is the frame applied to `lixKGLin`.** -/
theorem lixKHomotopy_at_zero (n k : ℕ) (dd : Fin ℓ → ℕ) (i : Fin (k + 1))
    {G : Gen.baseM n dd → Matrix (Gen.VIdx n dd) (Gen.VIdx n dd) ℂ}
    (hGc : Continuous G) (hGu : ∀ m, IsCornerUnitary (Gen.Vmat n m) (G m))
    (v : ↥(lixKU n k dd i hGc hGu)) :
    lixKHomotopyFun n k dd i hGc hGu (⟨(0 : ℝ), Set.left_mem_Icc.mpr zero_le_one⟩, v)
      = lixKFibreMap n k dd i hGc hGu (lixKGLin n k i hGc hGu (v : Fin (lixRank n dd) → ℂ)) := by
  have h0 : (0 : ChartSrc n × (∀ j : Fin ℓ, Fin (dd j) → ℂ))
      = ((0, 0) : ChartSrc n × (∀ j : Fin ℓ, Fin (dd j) → ℂ)) := rfl
  refine Subtype.ext (Prod.ext ?_ ?_)
  · show lixKBaseChart n k dd i ((0 : ℝ) • lixKQ n k dd i hGc hGu v) = lixKZero n k dd i
    rw [zero_smul, h0]
    exact lixKBaseChart_zero n k dd i
  · show lixKHomotopyVec n k dd i hGc hGu 0 v
      = lixKGFrame n k i hGc hGu *ᵥ lixKGLin n k i hGc hGu (v : Fin (lixRank n dd) → ℂ)
    rw [lixKGFrame_mulVec_lixKGLin, lixKHomotopyVec, zero_smul,
      lixKProductChart_lixKQ n k dd i hGc hGu v, h0, lixKBaseChart_zero n k dd i]
    rfl

/-! ## 6. The left leg: the section at the chart point -/

theorem lixKChartPt_mem (n k : ℕ) (dd : Fin ℓ → ℕ) (i : Fin (k + 1))
    {G : Gen.baseM n dd → Matrix (Gen.VIdx n dd) (Gen.VIdx n dd) ℂ}
    (hGc : Continuous G) (hGu : ∀ m, IsCornerUnitary (Gen.Vmat n m) (G m))
    (v : ↥(lixKU n k dd i hGc hGu)) :
    lixKBC n k dd i (lixKQ n k dd i hGc hGu v) ∈ lixKTrivBall n k dd i hGc hGu :=
  lixKBC_image_lixKHsqBall_subset n k dd i hGc hGu ⟨_, lixKQ_mem n k dd i hGc hGu v, rfl⟩

theorem continuous_lixKChartPtFun (n k : ℕ) (dd : Fin ℓ → ℕ) (i : Fin (k + 1))
    {G : Gen.baseM n dd → Matrix (Gen.VIdx n dd) (Gen.VIdx n dd) ℂ}
    (hGc : Continuous G) (hGu : ∀ m, IsCornerUnitary (Gen.Vmat n m) (G m)) :
    Continuous fun v : ↥(lixKU n k dd i hGc hGu) =>
      lixKBC n k dd i (lixKQ n k dd i hGc hGu v) :=
  (lixKBC n k dd i).continuousOn.comp_continuous (continuous_lixKQ n k dd i hGc hGu)
    (fun v => lixKHsqBall_subset_bc_source n k dd i hGc hGu (lixKQ_mem n k dd i hGc hGu v))

/-- **The chart point, into the neighbourhood of the `i`-th zero.** -/
def lixKChartPt (n k : ℕ) (dd : Fin ℓ → ℕ) (i : Fin (k + 1))
    {G : Gen.baseM n dd → Matrix (Gen.VIdx n dd) (Gen.VIdx n dd) ℂ}
    (hGc : Continuous G) (hGu : ∀ m, IsCornerUnitary (Gen.Vmat n m) (G m)) :
    TopCat.of ↥(lixKU n k dd i hGc hGu) ⟶ TopCat.of ↥(lixKTrivBall n k dd i hGc hGu) :=
  cmap (⟨fun v => ⟨lixKBC n k dd i (lixKQ n k dd i hGc hGu v),
      lixKChartPt_mem n k dd i hGc hGu v⟩,
    (continuous_lixKChartPtFun n k dd i hGc hGu).subtype_mk _⟩ :
      C(↥(lixKU n k dd i hGc hGu), ↥(lixKTrivBall n k dd i hGc hGu)))

/-- **Off the origin, the chart point misses every zero**: the `i`-th because the chart is
injective on its source and sends the origin to it, the others because the neighbourhood holds
none of them. -/
theorem lixKChartPt_mapsTo (n k : ℕ) (dd : Fin ℓ → ℕ) (i : Fin (k + 1))
    {G : Gen.baseM n dd → Matrix (Gen.VIdx n dd) (Gen.VIdx n dd) ℂ}
    (hGc : Continuous G) (hGu : ∀ m, IsCornerUnitary (Gen.Vmat n m) (G m)) :
    ∀ x ∈ ((Subtype.val : ↥(lixKU n k dd i hGc hGu) → (Fin (lixRank n dd) → ℂ)) ⁻¹'
        ({0}ᶜ : Set (Fin (lixRank n dd) → ℂ))),
      (ConcreteCategory.hom (lixKChartPt n k dd i hGc hGu)) x
        ∈ ((Subtype.val : ↥(lixKTrivBall n k dd i hGc hGu) → (↥sphereOne × Gen.baseM n dd)) ⁻¹'
          ((lixKZeroSet n k dd)ᶜ : Set (↥sphereOne × Gen.baseM n dd))) := by
  intro x hx hmem
  obtain ⟨j, hj⟩ := (mem_lixKZeroSet_iff n k dd _).mp hmem
  have hj' : lixKBC n k dd i (lixKQ n k dd i hGc hGu x) = lixKZero n k dd j := hj
  have hball : lixKBC n k dd i (lixKQ n k dd i hGc hGu x) ∈ lixKTrivBall n k dd i hGc hGu :=
    lixKChartPt_mem n k dd i hGc hGu x
  by_cases hji : j = i
  · rw [hji] at hj'
    have hsrc : lixKQ n k dd i hGc hGu x ∈ (lixKBC n k dd i).source :=
      lixKHsqBall_subset_bc_source n k dd i hGc hGu (lixKQ_mem n k dd i hGc hGu x)
    have heq : lixKBC n k dd i (lixKQ n k dd i hGc hGu x)
        = lixKBC n k dd i ((0, 0) : ChartSrc n × (∀ j : Fin ℓ, Fin (dd j) → ℂ)) := by
      rw [hj', lixKBC_apply]
      exact (lixKBaseChart_zero n k dd i).symm
    have hq0 : lixKQ n k dd i hGc hGu x
        = ((0, 0) : ChartSrc n × (∀ j : Fin ℓ, Fin (dd j) → ℂ)) :=
      (lixKBC n k dd i).injOn hsrc (zero_mem_lixKBC_source n k dd i) heq
    refine hx ?_
    have h1 : lixKFC n k dd i (lixKQ n k dd i hGc hGu x) = (x : Fin (lixRank n dd) → ℂ) :=
      (lixKFC n k dd i).right_inv (lixKU_subset_target n k dd i hGc hGu x.2)
    rw [hq0] at h1
    have h2 : lixKFC n k dd i ((0, 0) : ChartSrc n × (∀ j : Fin ℓ, Fin (dd j) → ℂ))
        = (0 : Fin (lixRank n dd) → ℂ) := lixKFullChart_zero n dd
    show (x : Fin (lixRank n dd) → ℂ) = 0
    rw [← h1, h2]
  · rw [hj'] at hball
    exact lixKZero_notMem_lixKTrivBall n k dd i hGc hGu j hji hball

/-- **The left leg**: the section at the chart point. -/
def lixKGLmap (n k : ℕ) (dd : Fin ℓ → ℕ) (i : Fin (k + 1))
    {G : Gen.baseM n dd → Matrix (Gen.VIdx n dd) (Gen.VIdx n dd) ℂ}
    (hGc : Continuous G) (hGu : ∀ m, IsCornerUnitary (Gen.Vmat n m) (G m))
    (hGe : ∀ m, G m *ᵥ Sum.elim (aVecK n m) 0 = Sum.elim (bVecK n k m) 0) :
    TopCat.of ↥(lixKU n k dd i hGc hGu) ⟶ lixTotalPair n hGc hGu :=
  lixKChartPt n k dd i hGc hGu ≫
    (sInclusion (X := lixN n dd) (lixKTrivBall n k dd i hGc hGu) ≫ lixKS n k hGc hGu hGe)

theorem lixKGL_mapsTo (n k : ℕ) (dd : Fin ℓ → ℕ) (i : Fin (k + 1))
    {G : Gen.baseM n dd → Matrix (Gen.VIdx n dd) (Gen.VIdx n dd) ℂ}
    (hGc : Continuous G) (hGu : ∀ m, IsCornerUnitary (Gen.Vmat n m) (G m))
    (hGe : ∀ m, G m *ᵥ Sum.elim (aVecK n m) 0 = Sum.elim (bVecK n k m) 0) :
    ∀ x ∈ ((Subtype.val : ↥(lixKU n k dd i hGc hGu) → (Fin (lixRank n dd) → ℂ)) ⁻¹'
        ({0}ᶜ : Set (Fin (lixRank n dd) → ℂ))),
      (ConcreteCategory.hom (lixKGLmap n k dd i hGc hGu hGe)) x
        ∈ lixPuncturedInTotal n hGc hGu :=
  fun x hx => lixKSectionTotal_mapsTo n k hGc hGu hGe _
    (lixKChartPt_mapsTo n k dd i hGc hGu x hx)

theorem lixKGLmap_apply (n k : ℕ) (dd : Fin ℓ → ℕ) (i : Fin (k + 1))
    {G : Gen.baseM n dd → Matrix (Gen.VIdx n dd) (Gen.VIdx n dd) ℂ}
    (hGc : Continuous G) (hGu : ∀ m, IsCornerUnitary (Gen.Vmat n m) (G m))
    (hGe : ∀ m, G m *ᵥ Sum.elim (aVecK n m) 0 = Sum.elim (bVecK n k m) 0)
    (v : ↥(lixKU n k dd i hGc hGu)) :
    (ConcreteCategory.hom (lixKGLmap n k dd i hGc hGu hGe)) v
      = lixKSectionTotal n k hGc hGu hGe (lixKBC n k dd i (lixKQ n k dd i hGc hGu v)) := rfl

/-! ## 7. The right leg: the fibre over the `i`-th zero -/

/-- The inclusion of the section chart's target. -/
def lixKIncF (n k : ℕ) (dd : Fin ℓ → ℕ) (i : Fin (k + 1)) :
    TopCat.of ↥(lixKFC n k dd i).target ⟶ TopCat.of (Fin (lixRank n dd) → ℂ) :=
  sInclusion (X := TopCat.of (Fin (lixRank n dd) → ℂ)) ((lixKFC n k dd i).target)

theorem lixKIncF_mapsTo (n k : ℕ) (dd : Fin ℓ → ℕ) (i : Fin (k + 1)) :
    ∀ x ∈ ((Subtype.val : ↥(lixKFC n k dd i).target → (Fin (lixRank n dd) → ℂ)) ⁻¹'
        ({(0 : Fin (lixRank n dd) → ℂ)}ᶜ)),
      (ConcreteCategory.hom (lixKIncF n k dd i)) x ∈ puncturedSet (lixRank n dd) :=
  fun _ hx => hx

/-- The trivialisation's inverse over the neighbourhood of the `i`-th zero. -/
def lixKTrivInv (n k : ℕ) (dd : Fin ℓ → ℕ) (i : Fin (k + 1))
    {G : Gen.baseM n dd → Matrix (Gen.VIdx n dd) (Gen.VIdx n dd) ℂ}
    (hGc : Continuous G) (hGu : ∀ m, IsCornerUnitary (Gen.Vmat n m) (G m)) :
    TopCat.of (↥(lixKTrivBall n k dd i hGc hGu) × (Fin (lixRank n dd) → ℂ)) ⟶
      TopCat.of (Bundle.Total
        ((lixBundle n G hGc hGu).restrictTo (lixKTrivBall n k dd i hGc hGu))) :=
  (TopCat.isoOfHomeo (Bundle.totalTrivStdOn (lixBundle n G hGc hGu) (lixKZero n k dd i)
    (lixKTrivBall n k dd i hGc hGu) (lixKTrivBall_subset n k dd i hGc hGu) (lixRank n dd)
    (rank_lixBundle n G hGc hGu _))).inv

/-- The inclusion of the restricted total space. -/
def lixKInclOn (n k : ℕ) (dd : Fin ℓ → ℕ) (i : Fin (k + 1))
    {G : Gen.baseM n dd → Matrix (Gen.VIdx n dd) (Gen.VIdx n dd) ℂ}
    (hGc : Continuous G) (hGu : ∀ m, IsCornerUnitary (Gen.Vmat n m) (G m)) :
    TopCat.of (Bundle.Total
        ((lixBundle n G hGc hGu).restrictTo (lixKTrivBall n k dd i hGc hGu))) ⟶
      lixTotalPair n hGc hGu :=
  cmap (Bundle.totalInclOn (lixBundle n G hGc hGu) (lixKTrivBall n k dd i hGc hGu))

theorem lixKTrivInv_mapsTo (n k : ℕ) (dd : Fin ℓ → ℕ) (i : Fin (k + 1))
    {G : Gen.baseM n dd → Matrix (Gen.VIdx n dd) (Gen.VIdx n dd) ℂ}
    (hGc : Continuous G) (hGu : ∀ m, IsCornerUnitary (Gen.Vmat n m) (G m)) :
    ∀ q ∈ {q : ↥(lixKTrivBall n k dd i hGc hGu) × (Fin (lixRank n dd) → ℂ) | q.2 ≠ 0},
      (ConcreteCategory.hom (lixKTrivInv n k dd i hGc hGu)) q ∈
        {w : Bundle.Total ((lixBundle n G hGc hGu).restrictTo (lixKTrivBall n k dd i hGc hGu)) |
          (w : ↥(lixKTrivBall n k dd i hGc hGu) × (Gen.VIdx n dd ⊕ Gen.VIdx n dd → ℂ))
            ∈ Bundle.puncturedSet
              ((lixBundle n G hGc hGu).restrictTo (lixKTrivBall n k dd i hGc hGu))} := by
  intro q hq
  refine ⟨((Bundle.totalTrivStdOn (lixBundle n G hGc hGu) (lixKZero n k dd i)
    (lixKTrivBall n k dd i hGc hGu) (lixKTrivBall_subset n k dd i hGc hGu) (lixRank n dd)
    (rank_lixBundle n G hGc hGu _)).symm q).2, ?_⟩
  intro hzero
  refine hq ?_
  have h := (Bundle.totalTrivStdOn_snd_eq_zero_iff (lixBundle n G hGc hGu) (lixKZero n k dd i)
    (lixKTrivBall n k dd i hGc hGu) (lixKTrivBall_subset n k dd i hGc hGu) (lixRank n dd)
    (rank_lixBundle n G hGc hGu _)
    ((Bundle.totalTrivStdOn (lixBundle n G hGc hGu) (lixKZero n k dd i)
      (lixKTrivBall n k dd i hGc hGu) (lixKTrivBall_subset n k dd i hGc hGu) (lixRank n dd)
      (rank_lixBundle n G hGc hGu _)).symm q)).mpr hzero
  rwa [Homeomorph.apply_symm_apply] at h

theorem lixKInclOn_mapsTo (n k : ℕ) (dd : Fin ℓ → ℕ) (i : Fin (k + 1))
    {G : Gen.baseM n dd → Matrix (Gen.VIdx n dd) (Gen.VIdx n dd) ℂ}
    (hGc : Continuous G) (hGu : ∀ m, IsCornerUnitary (Gen.Vmat n m) (G m)) :
    ∀ w ∈ {w : Bundle.Total ((lixBundle n G hGc hGu).restrictTo (lixKTrivBall n k dd i hGc hGu)) |
        (w : ↥(lixKTrivBall n k dd i hGc hGu) × (Gen.VIdx n dd ⊕ Gen.VIdx n dd → ℂ))
          ∈ Bundle.puncturedSet
            ((lixBundle n G hGc hGu).restrictTo (lixKTrivBall n k dd i hGc hGu))},
      (ConcreteCategory.hom (lixKInclOn n k dd i hGc hGu)) w ∈ lixPuncturedInTotal n hGc hGu :=
  fun w hw => (Bundle.totalInclOn_mem_puncturedSet_iff (lixBundle n G hGc hGu)
    (lixKTrivBall n k dd i hGc hGu) w).mpr hw

/-- **The right leg**: restrict to `lixKU`, include, slice at the `i`-th zero, trivialise back,
include the restricted total space. -/
def lixKGRmap (n k : ℕ) (dd : Fin ℓ → ℕ) (i : Fin (k + 1))
    {G : Gen.baseM n dd → Matrix (Gen.VIdx n dd) (Gen.VIdx n dd) ℂ}
    (hGc : Continuous G) (hGu : ∀ m, IsCornerUnitary (Gen.Vmat n m) (G m)) :
    TopCat.of ↥(lixKU n k dd i hGc hGu) ⟶ lixTotalPair n hGc hGu :=
  lixKShrinkMap n k dd i hGc hGu ≫ (lixKIncF n k dd i ≫
    (RelativeSupport.sliceMap (lixKZeroInBall n k dd i hGc hGu) (Fin (lixRank n dd) → ℂ) ≫
      (lixKTrivInv n k dd i hGc hGu ≫ lixKInclOn n k dd i hGc hGu)))

/-- The right leg without the trivialisation, which is what it computes to. -/
def lixKGRmap' (n k : ℕ) (dd : Fin ℓ → ℕ) (i : Fin (k + 1))
    {G : Gen.baseM n dd → Matrix (Gen.VIdx n dd) (Gen.VIdx n dd) ℂ}
    (hGc : Continuous G) (hGu : ∀ m, IsCornerUnitary (Gen.Vmat n m) (G m)) :
    TopCat.of ↥(lixKU n k dd i hGc hGu) ⟶ lixTotalPair n hGc hGu :=
  (lixKShrinkMap n k dd i hGc hGu ≫ lixKIncF n k dd i) ≫ cmap (lixKFibreMap n k dd i hGc hGu)

/-- The far end of the homotopy: the right leg precomposed with the linear automorphism. -/
def lixKFarMap (n k : ℕ) (dd : Fin ℓ → ℕ) (i : Fin (k + 1))
    {G : Gen.baseM n dd → Matrix (Gen.VIdx n dd) (Gen.VIdx n dd) ℂ}
    (hGc : Continuous G) (hGu : ∀ m, IsCornerUnitary (Gen.Vmat n m) (G m)) :
    TopCat.of ↥(lixKU n k dd i hGc hGu) ⟶ lixTotalPair n hGc hGu :=
  (lixKShrinkMap n k dd i hGc hGu ≫ lixKIncF n k dd i) ≫
    (lixKGMap n k i hGc hGu ≫ cmap (lixKFibreMap n k dd i hGc hGu))

theorem lixKSplit_mapsTo (n k : ℕ) (dd : Fin ℓ → ℕ) (i : Fin (k + 1))
    {G : Gen.baseM n dd → Matrix (Gen.VIdx n dd) (Gen.VIdx n dd) ℂ}
    (hGc : Continuous G) (hGu : ∀ m, IsCornerUnitary (Gen.Vmat n m) (G m)) :
    ∀ x ∈ ((Subtype.val : ↥(lixKU n k dd i hGc hGu) → (Fin (lixRank n dd) → ℂ)) ⁻¹'
        ({(0 : Fin (lixRank n dd) → ℂ)}ᶜ)),
      (ConcreteCategory.hom (lixKShrinkMap n k dd i hGc hGu ≫ lixKIncF n k dd i)) x
        ∈ puncturedSet (lixRank n dd) :=
  fun x hx => lixKIncF_mapsTo n k dd i _ (lixKShrink_mapsTo n k dd i hGc hGu x hx)

theorem lixKGFibre_mapsTo (n k : ℕ) (dd : Fin ℓ → ℕ) (i : Fin (k + 1))
    {G : Gen.baseM n dd → Matrix (Gen.VIdx n dd) (Gen.VIdx n dd) ℂ}
    (hGc : Continuous G) (hGu : ∀ m, IsCornerUnitary (Gen.Vmat n m) (G m)) :
    ∀ y ∈ puncturedSet (lixRank n dd),
      (ConcreteCategory.hom (lixKGMap n k i hGc hGu ≫ cmap (lixKFibreMap n k dd i hGc hGu))) y
        ∈ lixPuncturedInTotal n hGc hGu :=
  fun y hy => lixKFibreMap_mapsTo n k dd i hGc hGu _ (lixKGHomeo_mapsTo n k i hGc hGu y hy)

theorem lixKGR_mapsTo (n k : ℕ) (dd : Fin ℓ → ℕ) (i : Fin (k + 1))
    {G : Gen.baseM n dd → Matrix (Gen.VIdx n dd) (Gen.VIdx n dd) ℂ}
    (hGc : Continuous G) (hGu : ∀ m, IsCornerUnitary (Gen.Vmat n m) (G m)) :
    ∀ x ∈ ((Subtype.val : ↥(lixKU n k dd i hGc hGu) → (Fin (lixRank n dd) → ℂ)) ⁻¹'
        ({(0 : Fin (lixRank n dd) → ℂ)}ᶜ)),
      (ConcreteCategory.hom (lixKGRmap n k dd i hGc hGu)) x ∈ lixPuncturedInTotal n hGc hGu :=
  fun x hx =>
    lixKInclOn_mapsTo n k dd i hGc hGu _
      (lixKTrivInv_mapsTo n k dd i hGc hGu _
        (RelativeSupport.slice_mapsTo (lixKZeroInBall n k dd i hGc hGu)
          (puncturedSet (lixRank n dd)) _
          (lixKIncF_mapsTo n k dd i _ (lixKShrink_mapsTo n k dd i hGc hGu x hx))))

theorem lixKGR'_mapsTo (n k : ℕ) (dd : Fin ℓ → ℕ) (i : Fin (k + 1))
    {G : Gen.baseM n dd → Matrix (Gen.VIdx n dd) (Gen.VIdx n dd) ℂ}
    (hGc : Continuous G) (hGu : ∀ m, IsCornerUnitary (Gen.Vmat n m) (G m)) :
    ∀ x ∈ ((Subtype.val : ↥(lixKU n k dd i hGc hGu) → (Fin (lixRank n dd) → ℂ)) ⁻¹'
        ({(0 : Fin (lixRank n dd) → ℂ)}ᶜ)),
      (ConcreteCategory.hom (lixKGRmap' n k dd i hGc hGu)) x ∈ lixPuncturedInTotal n hGc hGu :=
  fun x hx => lixKFibreMap_mapsTo n k dd i hGc hGu _ (lixKSplit_mapsTo n k dd i hGc hGu x hx)

theorem lixKFar_mapsTo (n k : ℕ) (dd : Fin ℓ → ℕ) (i : Fin (k + 1))
    {G : Gen.baseM n dd → Matrix (Gen.VIdx n dd) (Gen.VIdx n dd) ℂ}
    (hGc : Continuous G) (hGu : ∀ m, IsCornerUnitary (Gen.Vmat n m) (G m)) :
    ∀ x ∈ ((Subtype.val : ↥(lixKU n k dd i hGc hGu) → (Fin (lixRank n dd) → ℂ)) ⁻¹'
        ({(0 : Fin (lixRank n dd) → ℂ)}ᶜ)),
      (ConcreteCategory.hom (lixKFarMap n k dd i hGc hGu)) x ∈ lixPuncturedInTotal n hGc hGu :=
  fun x hx => lixKGFibre_mapsTo n k dd i hGc hGu _ (lixKSplit_mapsTo n k dd i hGc hGu x hx)

/-- **The trivialisation's inverse over the `i`-th zero is the frame.**  Proved forward, through
`Homeomorph.symm_apply_eq`. -/
theorem lixKTrivInv_apply (n k : ℕ) (dd : Fin ℓ → ℕ) (i : Fin (k + 1))
    {G : Gen.baseM n dd → Matrix (Gen.VIdx n dd) (Gen.VIdx n dd) ℂ}
    (hGc : Continuous G) (hGu : ∀ m, IsCornerUnitary (Gen.Vmat n m) (G m))
    (y : Fin (lixRank n dd) → ℂ) :
    (ConcreteCategory.hom (lixKTrivInv n k dd i hGc hGu)) (lixKZeroInBall n k dd i hGc hGu, y)
      = ⟨(lixKZeroInBall n k dd i hGc hGu, lixKGFrame n k i hGc hGu *ᵥ y),
          lixKFibre_mem n k dd i hGc hGu y⟩ := by
  refine (Homeomorph.symm_apply_eq _).mpr ?_
  refine Prod.ext rfl ?_
  show y = (lixKGFrame n k i hGc hGu)ᴴ *ᵥ
    (Bundle.intert (lixBundle n G hGc hGu) (lixKZero n k dd i) (lixKZero n k dd i)
      *ᵥ (lixKGFrame n k i hGc hGu *ᵥ y))
  rw [Bundle.intert_self, Matrix.one_mulVec, Matrix.mulVec_mulVec,
    lixKGFrame_conjTranspose_mul, Matrix.one_mulVec]

/-- **The right leg is the fibre map**: the intertwiner at the point itself is the identity. -/
theorem lixKGRmap_eq (n k : ℕ) (dd : Fin ℓ → ℕ) (i : Fin (k + 1))
    {G : Gen.baseM n dd → Matrix (Gen.VIdx n dd) (Gen.VIdx n dd) ℂ}
    (hGc : Continuous G) (hGu : ∀ m, IsCornerUnitary (Gen.Vmat n m) (G m)) :
    lixKGRmap n k dd i hGc hGu = lixKGRmap' n k dd i hGc hGu := by
  apply TopCat.hom_ext
  apply ContinuousMap.ext
  intro v
  show (ConcreteCategory.hom (lixKInclOn n k dd i hGc hGu))
      ((ConcreteCategory.hom (lixKTrivInv n k dd i hGc hGu))
        (lixKZeroInBall n k dd i hGc hGu, (v : Fin (lixRank n dd) → ℂ)))
    = lixKFibreMap n k dd i hGc hGu (v : Fin (lixRank n dd) → ℂ)
  rw [lixKTrivInv_apply n k dd i hGc hGu]
  rfl

theorem lixKFarMap_apply (n k : ℕ) (dd : Fin ℓ → ℕ) (i : Fin (k + 1))
    {G : Gen.baseM n dd → Matrix (Gen.VIdx n dd) (Gen.VIdx n dd) ℂ}
    (hGc : Continuous G) (hGu : ∀ m, IsCornerUnitary (Gen.Vmat n m) (G m))
    (v : ↥(lixKU n k dd i hGc hGu)) :
    (ConcreteCategory.hom (lixKFarMap n k dd i hGc hGu)) v
      = lixKFibreMap n k dd i hGc hGu (lixKGLin n k i hGc hGu (v : Fin (lixRank n dd) → ℂ)) :=
  rfl

/-! ## 8. The homotopy's two ends are the two legs -/

theorem lixKHomotopy_end_one (n k : ℕ) (dd : Fin ℓ → ℕ) (i : Fin (k + 1))
    {G : Gen.baseM n dd → Matrix (Gen.VIdx n dd) (Gen.VIdx n dd) ℂ}
    (hGc : Continuous G) (hGu : ∀ m, IsCornerUnitary (Gen.Vmat n m) (G m))
    (hGe : ∀ m, G m *ᵥ Sum.elim (aVecK n m) 0 = Sum.elim (bVecK n k m) 0) :
    RelativeSupport.sliceMap (⟨(1 : ℝ), Set.right_mem_Icc.mpr zero_le_one⟩ : ↥lixI)
        (↥(lixKU n k dd i hGc hGu)) ≫ cmap (lixKHomotopyFun n k dd i hGc hGu)
      = lixKGLmap n k dd i hGc hGu hGe := by
  apply TopCat.hom_ext
  apply ContinuousMap.ext
  intro v
  exact (lixKHomotopy_at_one n k dd i hGc hGu hGe v).trans
    (lixKGLmap_apply n k dd i hGc hGu hGe v).symm

theorem lixKHomotopy_end_zero (n k : ℕ) (dd : Fin ℓ → ℕ) (i : Fin (k + 1))
    {G : Gen.baseM n dd → Matrix (Gen.VIdx n dd) (Gen.VIdx n dd) ℂ}
    (hGc : Continuous G) (hGu : ∀ m, IsCornerUnitary (Gen.Vmat n m) (G m)) :
    RelativeSupport.sliceMap (⟨(0 : ℝ), Set.left_mem_Icc.mpr zero_le_one⟩ : ↥lixI)
        (↥(lixKU n k dd i hGc hGu)) ≫ cmap (lixKHomotopyFun n k dd i hGc hGu)
      = lixKFarMap n k dd i hGc hGu := by
  apply TopCat.hom_ext
  apply ContinuousMap.ext
  intro v
  exact (lixKHomotopy_at_zero n k dd i hGc hGu v).trans
    (lixKFarMap_apply n k dd i hGc hGu v).symm

end KGen

/-! Audited on every build. -/

#audit_axioms KGen.lixKHomotopy_mapsTo
#audit_axioms KGen.lixKHomotopy_at_one
#audit_axioms KGen.lixKHomotopy_at_zero
#audit_axioms KGen.lixKChartPt_mapsTo
#audit_axioms KGen.lixKGRmap_eq
#audit_axioms KGen.lixKHomotopy_end_one
#audit_axioms KGen.lixKHomotopy_end_zero

end GroupApproximation.CharClass
