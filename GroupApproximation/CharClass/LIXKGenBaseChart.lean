import GroupApproximation.CharClass.LIXKGenZeroChartHomeo
import GroupApproximation.CharClass.LIXKGenLocalHomeo
import GroupApproximation.CharClass.LIXKGenBundle
import GroupApproximation.CharClass.LIXBaseChartHomeo
import GroupApproximation.CharClass.LIXProductChart
import GroupApproximation.CharClass.RelativeLocal
import GroupApproximation.CharClass.RelativeLocalModel
import GroupApproximation.Meta.AxiomGuard

/-!
# The relative group at each of the `k+1` zeros, identified with the local model, at rank `n`

Lane `lix-oddside-n`.  This is the rank-`n`, `k`-zero counterpart of `CharClass/LIXBaseChartHomeo`,
`LIXFullChart`, `LIXExcisionChart` and `LIXChartIso`, and it supplies the binders `exc i` and
`chartIso i` of `KGen.lixK_topClass_ne_zero_two` at every zero.

At the `i`-th zero `lixKZero n k dd i = (southPole, (ζ_i e₀, basePoint))` the base chart is the
circle chart times the chart at the `i`-th zero (`KGen.zeroChartHomeo`) times the projective tower
chart; the section chart is the product of the one-zero local homeomorphism
`KGen.eulerLocalHomeo n` with the projective block `cpLocalHomeo dd`, followed by a coordinate
change onto `Fin (lixRank n dd) → ℂ`.  Restricted to a common source the two give homeomorphic
neighbourhoods of the zero and of the origin, and

```text
H^q(N, N ∖ z_i) ≅ H^q(U, U ∖ z_i) ≅ H^q(V, V ∖ 0) ≅ H^q(ℂ^r, ℂ^r ∖ 0)
```

is excision, the homeomorphism of punctured pairs, and excision back.  The same section chart
serves every `i`; only the base chart depends on `i`, through `zeroChartHomeo n k i`.

## Main declarations

* `KGen.lixKBaseChart n k dd i`, `lixKBaseChart_zero = lixKZero n k dd i`.
* `KGen.lixKFullChart n dd`, `lixKFullChart_zero`.
* `KGen.lixKNbhdHomeo n k dd i`, `KGen.lixKRelModelIso n k dd i q` — **the identification.**
-/

noncomputable section

namespace GroupApproximation.CharClass

namespace KGen

open Set CategoryTheory
open GroupApproximation.STW59

set_option linter.unusedSectionVars false

variable {ℓ : ℕ}

instance instT1SpaceLixN (n : ℕ) (dd : Fin ℓ → ℕ) : T1Space ↥(lixN n dd) :=
  inferInstanceAs (T1Space (↥sphereOne × Gen.baseM n dd))

/-! ## 1. The base chart at the `i`-th zero -/

/-- The chart source, with the circle coordinate brought to the front. -/
def lixKChartReorder (n : ℕ) (dd : Fin ℓ → ℕ) :
    (ChartSrc n × (∀ j : Fin ℓ, Fin (dd j) → ℂ)) ≃ₜ
      (ℝ × (ChartBase n × (∀ j : Fin ℓ, Fin (dd j) → ℂ))) where
  toFun p := (p.1.2, (p.1.1, p.2))
  invFun q := ((q.2.1, q.1), q.2.2)
  left_inv _ := rfl
  right_inv _ := rfl
  continuous_toFun := by fun_prop
  continuous_invFun := by fun_prop

/-- **The base chart at the `i`-th zero.** -/
def lixKBaseChart (n k : ℕ) (dd : Fin ℓ → ℕ) (i : Fin (k + 1)) :
    OpenPartialHomeomorph (ChartSrc n × (∀ j : Fin ℓ, Fin (dd j) → ℂ))
      (↥sphereOne × Gen.baseM n dd) :=
  (lixKChartReorder n dd).toOpenPartialHomeomorph.trans
    (circChart.prod ((zeroChartHomeo n k i).prod (cpTowerChart dd)))

theorem zero_mem_lixKBaseChart_source (n k : ℕ) (dd : Fin ℓ → ℕ) (i : Fin (k + 1)) :
    ((0, 0) : ChartSrc n × (∀ j : Fin ℓ, Fin (dd j) → ℂ)) ∈ (lixKBaseChart n k dd i).source := by
  refine ⟨mem_univ _, ?_⟩
  refine ⟨?_, ?_, mem_univ _⟩
  · show (0 : ℝ) ∈ Ioo (-1 : ℝ) 1
    constructor <;> norm_num
  · show chartQ n (0 : ChartBase n) < 1
    simp [chartQ]

theorem lixKBaseChart_zero (n k : ℕ) (dd : Fin ℓ → ℕ) (i : Fin (k + 1)) :
    lixKBaseChart n k dd i ((0, 0) : ChartSrc n × (∀ j : Fin ℓ, Fin (dd j) → ℂ))
      = lixKZero n k dd i := by
  show (circChart 0, (zeroChartHomeo n k i 0, cpTowerChart dd 0)) = lixKZero n k dd i
  have h1 : circChart (0 : ℝ) = southPole := circChartFun_zero
  have h2 : zeroChartHomeo n k i (0 : ChartBase n) = kZero n k i := zeroChartHomeo_zero n k i
  have h3 : cpTowerChart dd (0 : ∀ j : Fin ℓ, Fin (dd j) → ℂ) = baseYPoint dd :=
    cpBaseChartFun_zero
  rw [h1, h2, h3]
  rfl

/-! ## 2. The section chart at full rank -/

theorem finrank_lixKProductTarget (n : ℕ) (dd : Fin ℓ → ℕ) :
    Module.finrank ℝ ((Fin (n + 1) → ℂ) × (∀ j : Fin ℓ, Fin (dd j) → ℂ))
      = Module.finrank ℝ (Fin (lixRank n dd) → ℂ) := by
  have h1 : ∀ m : ℕ, Module.finrank ℝ (Fin m → ℂ) = m * 2 := fun m => by
    simp [Module.finrank_pi_fintype, Complex.finrank_real_complex]
  have h2 : Module.finrank ℝ (∀ j : Fin ℓ, Fin (dd j) → ℂ) = ∑ j, dd j * 2 := by
    rw [Module.finrank_pi_fintype]
    exact Finset.sum_congr rfl fun j _ => h1 (dd j)
  rw [Module.finrank_prod, h1, h2, h1, lixRank, ← Finset.sum_mul]
  ring

/-- The coordinate change, from the dimension count alone. -/
def lixKCoordEquiv (n : ℕ) (dd : Fin ℓ → ℕ) :
    ((Fin (n + 1) → ℂ) × (∀ j : Fin ℓ, Fin (dd j) → ℂ)) ≃L[ℝ] (Fin (lixRank n dd) → ℂ) :=
  ContinuousLinearEquiv.ofFinrankEq (finrank_lixKProductTarget n dd)

/-- The product chart: the trivial block times the projective block. -/
def lixKProductChart (n : ℕ) (dd : Fin ℓ → ℕ) :
    OpenPartialHomeomorph (ChartSrc n × (∀ j : Fin ℓ, Fin (dd j) → ℂ))
      ((Fin (n + 1) → ℂ) × (∀ j : Fin ℓ, Fin (dd j) → ℂ)) :=
  (eulerLocalHomeo n).prod (cpLocalHomeo dd)

/-- **The chart of the section at its zero, in the local model's coordinates.** -/
def lixKFullChart (n : ℕ) (dd : Fin ℓ → ℕ) :
    OpenPartialHomeomorph (ChartSrc n × (∀ j : Fin ℓ, Fin (dd j) → ℂ))
      (Fin (lixRank n dd) → ℂ) :=
  (lixKProductChart n dd).transHomeomorph (lixKCoordEquiv n dd).toHomeomorph

theorem zero_mem_lixKFullChart_source (n : ℕ) (dd : Fin ℓ → ℕ) :
    ((0, 0) : ChartSrc n × (∀ j : Fin ℓ, Fin (dd j) → ℂ)) ∈ (lixKFullChart n dd).source :=
  ⟨zero_mem_eulerLocalHomeo_source n, zero_mem_cpLocalHomeo_source⟩

theorem lixKFullChart_zero (n : ℕ) (dd : Fin ℓ → ℕ) :
    lixKFullChart n dd ((0, 0) : ChartSrc n × (∀ j : Fin ℓ, Fin (dd j) → ℂ))
      = (0 : Fin (lixRank n dd) → ℂ) := by
  show (lixKCoordEquiv n dd) (lixKProductChart n dd (0, 0)) = 0
  have h : lixKProductChart n dd ((0, 0) : ChartSrc n × (∀ j : Fin ℓ, Fin (dd j) → ℂ))
      = ((0, 0) : (Fin (n + 1) → ℂ) × (∀ j : Fin ℓ, Fin (dd j) → ℂ)) :=
    Prod.ext (eulerLocalHomeo_zero n) cpLocalHomeo_zero
  rw [h]
  exact map_zero _

/-! ## 3. The two charts on a common source -/

/-- The base chart at the `i`-th zero, cut down to where the section chart is defined. -/
def lixKBC (n k : ℕ) (dd : Fin ℓ → ℕ) (i : Fin (k + 1)) :
    OpenPartialHomeomorph (ChartSrc n × (∀ j : Fin ℓ, Fin (dd j) → ℂ))
      (↥sphereOne × Gen.baseM n dd) :=
  (lixKBaseChart n k dd i).restrOpen (lixKFullChart n dd).source (lixKFullChart n dd).open_source

/-- The section chart, cut down the same way. -/
def lixKFC (n k : ℕ) (dd : Fin ℓ → ℕ) (i : Fin (k + 1)) :
    OpenPartialHomeomorph (ChartSrc n × (∀ j : Fin ℓ, Fin (dd j) → ℂ))
      (Fin (lixRank n dd) → ℂ) :=
  (lixKFullChart n dd).restrOpen (lixKBaseChart n k dd i).source
    (lixKBaseChart n k dd i).open_source

theorem lixKBC_source_eq_lixKFC_source (n k : ℕ) (dd : Fin ℓ → ℕ) (i : Fin (k + 1)) :
    (lixKBC n k dd i).source = (lixKFC n k dd i).source := by
  rw [lixKBC, lixKFC, OpenPartialHomeomorph.restrOpen_source,
    OpenPartialHomeomorph.restrOpen_source, inter_comm]

theorem zero_mem_lixKBC_source (n k : ℕ) (dd : Fin ℓ → ℕ) (i : Fin (k + 1)) :
    ((0, 0) : ChartSrc n × (∀ j : Fin ℓ, Fin (dd j) → ℂ)) ∈ (lixKBC n k dd i).source := by
  rw [lixKBC, OpenPartialHomeomorph.restrOpen_source]
  exact ⟨zero_mem_lixKBaseChart_source n k dd i, zero_mem_lixKFullChart_source n dd⟩

theorem zero_mem_lixKFC_source (n k : ℕ) (dd : Fin ℓ → ℕ) (i : Fin (k + 1)) :
    ((0, 0) : ChartSrc n × (∀ j : Fin ℓ, Fin (dd j) → ℂ)) ∈ (lixKFC n k dd i).source :=
  lixKBC_source_eq_lixKFC_source n k dd i ▸ zero_mem_lixKBC_source n k dd i

theorem lixKZero_mem_lixKBC_target (n k : ℕ) (dd : Fin ℓ → ℕ) (i : Fin (k + 1)) :
    lixKZero n k dd i ∈ (lixKBC n k dd i).target := by
  have h := (lixKBC n k dd i).map_source (zero_mem_lixKBC_source n k dd i)
  rwa [show lixKBC n k dd i ((0, 0) : ChartSrc n × (∀ j : Fin ℓ, Fin (dd j) → ℂ))
    = lixKZero n k dd i from lixKBaseChart_zero n k dd i] at h

theorem zero_mem_lixKFC_target (n k : ℕ) (dd : Fin ℓ → ℕ) (i : Fin (k + 1)) :
    (0 : Fin (lixRank n dd) → ℂ) ∈ (lixKFC n k dd i).target := by
  have h := (lixKFC n k dd i).map_source (zero_mem_lixKFC_source n k dd i)
  rwa [show lixKFC n k dd i ((0, 0) : ChartSrc n × (∀ j : Fin ℓ, Fin (dd j) → ℂ))
    = (0 : Fin (lixRank n dd) → ℂ) from lixKFullChart_zero n dd] at h

/-! ## 4. The neighbourhoods, and the identification -/

/-- **A neighbourhood of the `i`-th zero, homeomorphic to one of the origin.** -/
def lixKNbhdHomeo (n k : ℕ) (dd : Fin ℓ → ℕ) (i : Fin (k + 1)) :
    ↥(lixKBC n k dd i).target ≃ₜ ↥(lixKFC n k dd i).target :=
  (lixKBC n k dd i).toHomeomorphSourceTarget.symm.trans
    ((Homeomorph.setCongr (lixKBC_source_eq_lixKFC_source n k dd i)).trans
      (lixKFC n k dd i).toHomeomorphSourceTarget)

theorem lixKNbhdHomeo_zero (n k : ℕ) (dd : Fin ℓ → ℕ) (i : Fin (k + 1)) :
    (lixKNbhdHomeo n k dd i ⟨lixKZero n k dd i, lixKZero_mem_lixKBC_target n k dd i⟩ :
        ↥(lixKFC n k dd i).target)
      = ⟨(0 : Fin (lixRank n dd) → ℂ), zero_mem_lixKFC_target n k dd i⟩ := by
  refine Subtype.ext ?_
  show lixKFC n k dd i ((lixKBC n k dd i).symm (lixKZero n k dd i)) = _
  have hsym : (lixKBC n k dd i).symm (lixKZero n k dd i)
      = ((0, 0) : ChartSrc n × (∀ j : Fin ℓ, Fin (dd j) → ℂ)) := by
    rw [← lixKBaseChart_zero n k dd i]
    exact (lixKBC n k dd i).left_inv (zero_mem_lixKBC_source n k dd i)
  rw [hsym]
  exact lixKFullChart_zero n dd

/-- **The relative group at the `i`-th zero, identified with the local model**, in every
degree. -/
def lixKRelModelIso (n k : ℕ) (dd : Fin ℓ → ℕ) (i : Fin (k + 1)) (q : ℕ) :
    relCohomology (ZMod 2) (lixN n dd)
        ({lixKZero n k dd i}ᶜ : Set (↥sphereOne × Gen.baseM n dd)) q
      ≅ relCohomology (ZMod 2) (TopCat.of (Fin (lixRank n dd) → ℂ))
        (puncturedSet (lixRank n dd)) q :=
  (excisionIsoPoint (lixN n dd) (lixKZero n k dd i) (lixKBC n k dd i).target
      (lixKBC n k dd i).open_target (lixKZero_mem_lixKBC_target n k dd i) q).trans
    ((relCohomologyCongrPoint (lixKNbhdHomeo n k dd i) (lixKZero_mem_lixKBC_target n k dd i)
        (zero_mem_lixKFC_target n k dd i) (lixKNbhdHomeo_zero n k dd i) q).trans
      (excisionIsoPoint (TopCat.of (Fin (lixRank n dd) → ℂ)) 0 (lixKFC n k dd i).target
        (lixKFC n k dd i).open_target (zero_mem_lixKFC_target n k dd i) q).symm)

end KGen

/-! Audited on every build. -/

#audit_axioms KGen.lixKBaseChart_zero
#audit_axioms KGen.lixKFullChart_zero
#audit_axioms KGen.lixKNbhdHomeo_zero

end GroupApproximation.CharClass
