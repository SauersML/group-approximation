import Mathlib.MeasureTheory.Measure.DiracProba
import Mathlib.MeasureTheory.Measure.Prokhorov
import GroupApproximation.Analysis.STW22BauerSimplex

/-!
# The probability simplex of a compact metrizable space has a closed extreme boundary

This is the analytic half of step (A6) of the STW Problem XXII counterexample
audit (`research/artifacts/stw22-trace-problem-counterexample-audit-2026-08-31.md`).
The audit asserts

```text
T(A) = Prob(K),   ∂ₑ T(A) = K,
```

for `K` the one-point compactification of `⨆ₛ CP^(s²)`, and concludes that
`T(A)` is Bauer.  Everything in that sentence except the identification of
`T(A)` with `Prob(K)` is proved here, unconditionally, for an arbitrary compact
second-countable Hausdorff Borel space `K`:

* `convex_probSimplex`, `isCompact_probSimplex` — `Prob(K)` is a compact convex
  set;
* `extremePoints_probSimplex` — `∂ₑ Prob(K)` is **exactly** the set of Dirac
  masses, so the extreme boundary *is* `K`;
* `isClosed_extremePoints_probSimplex` — that boundary is closed, i.e. the Bauer
  clause;
* `isEmbedding_diracFM` — the identification `∂ₑ Prob(K) ≅ K` is a topological
  embedding, not merely a bijection.

## The ambient vector space

`Prob(K)` is realised as `{μ : FiniteMeasure K | μ.mass = 1}` inside Mathlib's
`MeasureTheory.FiniteMeasure K`, which carries the topology of weak convergence,
is Hausdorff, and is a module over `ℝ≥0`.  There is no larger *real* vector
space of measures available in Mathlib (no lattice structure on signed measures,
no Riesz-space completion), so the convexity notions are taken over `ℝ≥0`.  This
loses nothing: `openSegment` only ever uses strictly positive coefficients
summing to one, so a set inside a cone has the same extreme points computed over
`ℝ≥0` as over `ℝ`.

## What is proved and what is assumed

The Choquet (lattice-cone) clause of `IsBauerSimplex` is **not** proved here; it
is classical for `Prob(K)` — the cone of finite measures is a lattice by
Hahn--Jordan — but Mathlib has no lattice structure on measures to quote.  It is
carried as an explicit hypothesis of `isBauerSimplex_probSimplex`, and the
unconditional content is `isCompactConvexClosedBoundary_probSimplex`.

The hard inclusion `∂ₑ Prob(K) ⊆ {δₓ}` is proved from scratch:

1. an extreme point is `{0,1}`-valued, because a set `E` with `0 < μE < 1`
   splits `μ` as `μE · μ(·|E) + μEᶜ · μ(·|Eᶜ)` (`FiniteMeasure.restrict`);
2. a `{0,1}`-valued Borel probability measure on a second-countable T1 space is a
   Dirac mass: for a countable basis `B`, replacing each `B n` by whichever of
   `B n`, `(B n)ᶜ` has measure one and intersecting gives a measure-one set which
   separation forces to be a singleton.
-/

namespace GroupApproximation
namespace STW22

open MeasureTheory Set Topology TopologicalSpace

open scoped NNReal ENNReal

set_option linter.unusedSectionVars false

noncomputable section

variable {K : Type*} [MeasurableSpace K]

/-! ## The probability simplex inside the finite measures -/

variable (K) in
/-- The probability simplex of `K`, as a subset of the `ℝ≥0`-module of finite
Borel measures with the topology of weak convergence.  By
`MeasureTheory.ProbabilityMeasure.range_toFiniteMeasure` this is exactly the
image of `ProbabilityMeasure K`. -/
def probSimplex : Set (FiniteMeasure K) := {μ : FiniteMeasure K | μ.mass = 1}

theorem mem_probSimplex {μ : FiniteMeasure K} : μ ∈ probSimplex K ↔ μ.mass = 1 := Iff.rfl

/-- The total mass is additive. -/
theorem mass_add_eq (μ ν : FiniteMeasure K) : (μ + ν).mass = μ.mass + ν.mass := by
  simp only [FiniteMeasure.mass, FiniteMeasure.coeFn_add, Pi.add_apply]

/-- The total mass is homogeneous. -/
theorem mass_smul_eq (c : ℝ≥0) (μ : FiniteMeasure K) : (c • μ).mass = c * μ.mass := by
  simp only [FiniteMeasure.mass, FiniteMeasure.smul_apply, smul_eq_mul]

/-- A finite measure is the sum of its restrictions to a measurable set and its
complement. -/
theorem restrict_add_restrict_compl (μ : FiniteMeasure K) {E : Set K} (hE : MeasurableSet E) :
    μ.restrict E + μ.restrict Eᶜ = μ := by
  rw [← FiniteMeasure.restrict_union (disjoint_compl_right) hE.compl, union_compl_self,
    FiniteMeasure.restrict_univ]

/-- For a probability measure, the measures of a set and of its complement add
up to one. -/
theorem apply_add_apply_compl {μ : FiniteMeasure K} (hmass : μ.mass = 1) {E : Set K}
    (hE : MeasurableSet E) : μ E + μ Eᶜ = 1 := by
  have h := congrArg FiniteMeasure.mass (restrict_add_restrict_compl μ hE)
  rw [mass_add_eq, FiniteMeasure.restrict_mass, FiniteMeasure.restrict_mass, hmass] at h
  exact h

theorem convex_probSimplex : Convex ℝ≥0 (probSimplex K) := by
  intro μ hμ ν hν a b _ _ hab
  have hμ' : μ.mass = 1 := hμ
  have hν' : ν.mass = 1 := hν
  show (a • μ + b • ν).mass = 1
  rw [mass_add_eq, mass_smul_eq, mass_smul_eq, hμ', hν', mul_one, mul_one, hab]

/-- **Compactness of the trace simplex.**  On a compact space the probability
measures form a compact set; this is Mathlib's Riesz--Markov--Kakutani based
Prokhorov file. -/
theorem isCompact_probSimplex [TopologicalSpace K] [T2Space K] [BorelSpace K] [CompactSpace K] :
    IsCompact (probSimplex K) :=
  isCompact_setOf_finiteMeasure_eq_of_compactSpace K 1

/-! ## Dirac masses -/

/-- The Dirac mass at `x`, as a finite measure. -/
def diracFM (x : K) : FiniteMeasure K := (diracProba x).toFiniteMeasure

@[simp]
theorem diracFM_toMeasure (x : K) :
    ((diracFM x : FiniteMeasure K) : Measure K) = Measure.dirac x := rfl

theorem diracFM_mem_probSimplex (x : K) : diracFM x ∈ probSimplex K :=
  (diracProba x).mass_toFiniteMeasure

theorem diracFM_apply_singleton_self (x : K) : (diracFM x) ({x} : Set K) = 1 := by
  have h : (((diracFM x) ({x} : Set K) : ℝ≥0) : ℝ≥0∞) = 1 := by
    rw [FiniteMeasure.ennreal_coeFn_eq_coeFn_toMeasure, diracFM_toMeasure]
    exact Measure.dirac_apply_of_mem rfl
  exact_mod_cast h

/-- A probability measure putting full mass on a point is the Dirac mass there. -/
theorem eq_diracFM_of_apply_singleton [MeasurableSingletonClass K] {μ : FiniteMeasure K}
    (hmass : μ.mass = 1) {x : K} (hx : μ ({x} : Set K) = 1) : μ = diracFM x := by
  apply FiniteMeasure.toMeasure_injective
  rw [diracFM_toMeasure]
  have huniv : (μ : Measure K) univ = 1 := by
    rw [← FiniteMeasure.ennreal_mass, hmass, ENNReal.coe_one]
  have hxm : (μ : Measure K) ({x} : Set K) = 1 := by
    rw [← FiniteMeasure.ennreal_coeFn_eq_coeFn_toMeasure, hx, ENNReal.coe_one]
  have hcompl : (μ : Measure K) (({x} : Set K)ᶜ) = 0 := by
    rw [measure_compl (MeasurableSet.singleton x) (by rw [hxm]; exact ENNReal.one_ne_top),
      huniv, hxm, tsub_self]
  ext s hs
  rw [Measure.dirac_apply' x hs]
  by_cases hxs : x ∈ s
  · simp only [Set.indicator_of_mem hxs, Pi.one_apply]
    refine le_antisymm ?_ ?_
    · rw [← huniv]
      exact measure_mono (subset_univ s)
    · rw [← hxm]
      exact measure_mono (singleton_subset_iff.mpr hxs)
  · simp only [Set.indicator_of_notMem hxs]
    refine measure_mono_null (fun y hy => ?_) hcompl
    simp only [Set.mem_compl_iff, Set.mem_singleton_iff]
    rintro rfl
    exact hxs hy

/-- **Dirac masses are extreme.**  If `δₓ = a μ + b ν` with `a, b > 0`, then
both `μ` and `ν` must put full mass on `x`. -/
theorem diracFM_mem_extremePoints [MeasurableSingletonClass K] (x : K) :
    diracFM x ∈ (probSimplex K).extremePoints ℝ≥0 := by
  refine ⟨diracFM_mem_probSimplex x, ?_⟩
  intro μ hμ ν hν hseg
  obtain ⟨a, b, ha, hb, hab, hsum⟩ := hseg
  have hμ' : μ.mass = 1 := hμ
  have hν' : ν.mass = 1 := hν
  have h0 : (a • μ + b • ν) ({x} : Set K) = (diracFM x) ({x} : Set K) := by rw [hsum]
  simp only [FiniteMeasure.coeFn_add, Pi.add_apply, FiniteMeasure.smul_apply, smul_eq_mul] at h0
  rw [diracFM_apply_singleton_self x] at h0
  have hle1 : μ ({x} : Set K) ≤ 1 := by
    have h := FiniteMeasure.apply_le_mass μ ({x} : Set K)
    rwa [hμ'] at h
  have hle2 : ν ({x} : Set K) ≤ 1 := by
    have h := FiniteMeasure.apply_le_mass ν ({x} : Set K)
    rwa [hν'] at h
  have hone : μ ({x} : Set K) = 1 := by
    by_contra hne
    have hlt : μ ({x} : Set K) < 1 := lt_of_le_of_ne hle1 hne
    have hstrict : a * μ ({x} : Set K) + b * ν ({x} : Set K) < a * 1 + b * 1 :=
      add_lt_add_of_lt_of_le (mul_lt_mul_of_pos_left hlt ha)
        (mul_le_mul_of_nonneg_left hle2 hb.le)
    rw [mul_one, mul_one, hab] at hstrict
    exact absurd h0 (ne_of_lt hstrict)
  exact eq_diracFM_of_apply_singleton hμ' hone

/-! ## Extreme points are `{0,1}`-valued, hence Dirac -/

/-- An extreme point of the probability simplex takes only the values `0` and
`1`: otherwise conditioning on a set of intermediate mass splits it. -/
theorem apply_eq_zero_or_one_of_mem_extremePoints {μ : FiniteMeasure K}
    (hμ : μ ∈ (probSimplex K).extremePoints ℝ≥0) {E : Set K} (hE : MeasurableSet E) :
    μ E = 0 ∨ μ E = 1 := by
  have hmass : μ.mass = 1 := hμ.1
  by_contra hcon
  push_neg at hcon
  obtain ⟨h0, h1⟩ := hcon
  have hsum : μ E + μ Eᶜ = 1 := apply_add_apply_compl hmass hE
  have ht : (0 : ℝ≥0) < μ E := lt_of_le_of_ne (zero_le _) (Ne.symm h0)
  have hu : (0 : ℝ≥0) < μ Eᶜ := by
    rcases eq_or_lt_of_le (zero_le (μ Eᶜ)) with h | h
    · exact absurd (by rw [← hsum, ← h, add_zero]) h1
    · exact h
  have hm1 : ((μ E)⁻¹ • μ.restrict E) ∈ probSimplex K := by
    show ((μ E)⁻¹ • μ.restrict E).mass = 1
    rw [mass_smul_eq, FiniteMeasure.restrict_mass, inv_mul_cancel₀ ht.ne']
  have hm2 : ((μ Eᶜ)⁻¹ • μ.restrict Eᶜ) ∈ probSimplex K := by
    show ((μ Eᶜ)⁻¹ • μ.restrict Eᶜ).mass = 1
    rw [mass_smul_eq, FiniteMeasure.restrict_mass, inv_mul_cancel₀ hu.ne']
  have hseg : μ ∈ openSegment ℝ≥0 ((μ E)⁻¹ • μ.restrict E) ((μ Eᶜ)⁻¹ • μ.restrict Eᶜ) := by
    refine ⟨μ E, μ Eᶜ, ht, hu, hsum, ?_⟩
    rw [smul_smul, smul_smul, mul_inv_cancel₀ ht.ne', mul_inv_cancel₀ hu.ne', one_smul, one_smul]
    exact restrict_add_restrict_compl μ hE
  have hkey := hμ.2 hm1 hm2 hseg
  have hval : ((μ E)⁻¹ • μ.restrict E) E = 1 := by
    rw [FiniteMeasure.smul_apply, FiniteMeasure.restrict_apply _ _ hE, Set.inter_self,
      smul_eq_mul, inv_mul_cancel₀ ht.ne']
  rw [hkey] at hval
  exact h1 hval

/-- **The hard inclusion.**  An extreme point of the probability simplex of a
second-countable Hausdorff Borel space is a Dirac mass. -/
theorem exists_eq_diracFM_of_mem_extremePoints [TopologicalSpace K] [T2Space K]
    [SecondCountableTopology K] [BorelSpace K] {μ : FiniteMeasure K}
    (hμ : μ ∈ (probSimplex K).extremePoints ℝ≥0) : ∃ x : K, μ = diracFM x := by
  have hmass : μ.mass = 1 := hμ.1
  obtain ⟨B, hB⟩ := TopologicalSpace.exists_seq_basis K
  have hchoice : ∀ n : ℕ, ∃ W : Set K, MeasurableSet W ∧ μ W = 1 ∧ (W = B n ∨ W = (B n)ᶜ) := by
    intro n
    have hopen : MeasurableSet (B n) := (hB.isOpen (mem_range_self n)).measurableSet
    rcases apply_eq_zero_or_one_of_mem_extremePoints hμ hopen with h | h
    · refine ⟨(B n)ᶜ, hopen.compl, ?_, Or.inr rfl⟩
      have hadd := apply_add_apply_compl hmass hopen
      rw [h, zero_add] at hadd
      exact hadd
    · exact ⟨B n, hopen, h, Or.inl rfl⟩
  choose V hVmble hVone hVcases using hchoice
  have hVcompl : ∀ n, (μ : Measure K) (V n)ᶜ = 0 := by
    intro n
    have hz : μ (V n)ᶜ = 0 := by
      have h := apply_add_apply_compl hmass (hVmble n)
      rw [hVone n] at h
      have h2 : (1 : ℝ≥0) + μ (V n)ᶜ = 1 + 0 := by rw [add_zero]; exact h
      exact add_left_cancel h2
    rw [← FiniteMeasure.ennreal_coeFn_eq_coeFn_toMeasure, hz, ENNReal.coe_zero]
  have hmble : MeasurableSet (⋂ n, V n) := MeasurableSet.iInter hVmble
  have hnull : (μ : Measure K) ((⋂ n, V n)ᶜ) = 0 := by
    rw [Set.compl_iInter]
    exact measure_iUnion_null hVcompl
  have huniv : (μ : Measure K) univ = 1 := by
    rw [← FiniteMeasure.ennreal_mass, hmass, ENNReal.coe_one]
  have hone : (μ : Measure K) (⋂ n, V n) = 1 := by
    have h := measure_add_measure_compl (μ := (μ : Measure K)) hmble
    rw [hnull, add_zero, huniv] at h
    exact h
  have hne0 : (μ : Measure K) (⋂ n, V n) ≠ 0 := by
    rw [hone]
    exact one_ne_zero
  obtain ⟨x, hx⟩ : (⋂ n, V n).Nonempty := nonempty_of_measure_ne_zero hne0
  refine ⟨x, eq_diracFM_of_apply_singleton hmass ?_⟩
  have hsub : (⋂ n, V n) ⊆ ({x} : Set K) := by
    intro y hy
    rw [Set.mem_singleton_iff]
    by_contra hne
    have hxU : x ∈ (({y} : Set K)ᶜ) := by
      simp only [Set.mem_compl_iff, Set.mem_singleton_iff]
      exact fun h => hne h.symm
    obtain ⟨W, hWmem, hxW, hWU⟩ := hB.exists_subset_of_mem_open hxU isOpen_compl_singleton
    obtain ⟨n, rfl⟩ := hWmem
    rcases hVcases n with h | h
    · have hyB : y ∈ B n := by
        rw [← h]
        exact Set.mem_iInter.mp hy n
      exact (hWU hyB) rfl
    · have hxc : x ∈ (B n)ᶜ := by
        rw [← h]
        exact Set.mem_iInter.mp hx n
      exact hxc hxW
  have hge : (1 : ℝ≥0∞) ≤ (μ : Measure K) ({x} : Set K) := by
    rw [← hone]
    exact measure_mono hsub
  have hle : μ ({x} : Set K) ≤ 1 := by
    have h := FiniteMeasure.apply_le_mass μ ({x} : Set K)
    rwa [hmass] at h
  rw [← FiniteMeasure.ennreal_coeFn_eq_coeFn_toMeasure] at hge
  have hge' : (1 : ℝ≥0) ≤ μ ({x} : Set K) := by exact_mod_cast hge
  exact le_antisymm hle hge'

/-- **The extreme boundary of `Prob(K)` is `K`.**  This is `∂ₑ T(A) = K` of the
audit's (A6), for the probability-measure model of the trace simplex. -/
theorem extremePoints_probSimplex [TopologicalSpace K] [T2Space K] [SecondCountableTopology K]
    [BorelSpace K] :
    (probSimplex K).extremePoints ℝ≥0 = Set.range (diracFM (K := K)) := by
  apply Set.Subset.antisymm
  · intro μ hμ
    obtain ⟨x, hx⟩ := exists_eq_diracFM_of_mem_extremePoints hμ
    exact ⟨x, hx.symm⟩
  · rintro _ ⟨x, rfl⟩
    exact diracFM_mem_extremePoints x

/-! ## The Bauer clause -/

theorem continuous_diracFM [TopologicalSpace K] [OpensMeasurableSpace K] :
    Continuous (diracFM (K := K)) := by
  have h : Continuous
      ((ProbabilityMeasure.toFiniteMeasure : ProbabilityMeasure K → FiniteMeasure K) ∘
        (fun x : K => diracProba x)) :=
    ProbabilityMeasure.toFiniteMeasure_continuous.comp continuous_diracProba
  exact h

/-- The identification `K ≅ ∂ₑ Prob(K)` is a topological embedding, so the
extreme boundary carries exactly the topology of `K`. -/
theorem isEmbedding_diracFM [TopologicalSpace K] [T0Space K] [CompletelyRegularSpace K]
    [OpensMeasurableSpace K] : IsEmbedding (diracFM (K := K)) := by
  have h : IsEmbedding
      ((ProbabilityMeasure.toFiniteMeasure : ProbabilityMeasure K → FiniteMeasure K) ∘
        (fun x : K => diracProba x)) :=
    (ProbabilityMeasure.toFiniteMeasure_isEmbedding K).comp isEmbedding_diracProba
  exact h

theorem isCompact_range_diracFM [TopologicalSpace K] [OpensMeasurableSpace K] [CompactSpace K] :
    IsCompact (Set.range (diracFM (K := K))) :=
  isCompact_range continuous_diracFM

/-- **The Bauer clause.**  For `K` compact, second countable and Hausdorff, the
extreme boundary of `Prob(K)` is closed. -/
theorem isClosed_extremePoints_probSimplex [TopologicalSpace K] [T2Space K]
    [SecondCountableTopology K] [BorelSpace K] [CompactSpace K] [HasOuterApproxClosed K] :
    IsClosed ((probSimplex K).extremePoints ℝ≥0) := by
  rw [extremePoints_probSimplex]
  exact isCompact_range_diracFM.isClosed

/-- **Unconditional form of audit step (A6).**  `Prob(K)` is a compact convex set
with closed extreme boundary. -/
theorem isCompactConvexClosedBoundary_probSimplex [TopologicalSpace K] [T2Space K]
    [SecondCountableTopology K] [BorelSpace K] [CompactSpace K] [HasOuterApproxClosed K] :
    IsCompactConvexClosedBoundary ℝ≥0 (probSimplex K) :=
  ⟨convex_probSimplex, isCompact_probSimplex, isClosed_extremePoints_probSimplex⟩

/-- **Bauer.**  With the Choquet (lattice-cone) clause supplied — classical for
`Prob(K)` by Hahn--Jordan, and not available in Mathlib — the probability
simplex is a Bauer simplex. -/
theorem isBauerSimplex_probSimplex [TopologicalSpace K] [T2Space K]
    [SecondCountableTopology K] [BorelSpace K] [CompactSpace K] [HasOuterApproxClosed K]
    (hchoquet : IsChoquetSimplex ℝ≥0 (probSimplex K)) :
    IsBauerSimplex ℝ≥0 (probSimplex K) :=
  ⟨hchoquet, isCompactConvexClosedBoundary_probSimplex⟩

/-! ## Transport to an abstract trace simplex

The audit uses the Bauer property of `Prob(K)` for `T(A)`, through an
identification of the two.  What such an identification supplies is an injective,
additive, `ℝ≥0`-homogeneous, continuous map from `Prob(K)` onto `T(A)`; the
statement below says that this is enough, and is the exact interface that a
formalisation of `T(A) ≅ Prob(K)` has to meet.
-/

/-- If a trace simplex `T` is the image of `Prob(K)` under a continuous injective
map preserving sums and nonnegative scalars, then `T` is compact, convex, and has
a closed extreme boundary. -/
theorem isCompactConvexClosedBoundary_of_probSimplex_image
    [TopologicalSpace K] [T2Space K] [SecondCountableTopology K] [BorelSpace K]
    [CompactSpace K] [HasOuterApproxClosed K]
    {V : Type*} [AddCommMonoid V] [SMul ℝ≥0 V] [TopologicalSpace V] [T2Space V]
    (e : FiniteMeasure K → V) (hcont : Continuous e) (hinj : Function.Injective e)
    (hadd : ∀ x y : FiniteMeasure K, e (x + y) = e x + e y)
    (hsmul : ∀ (c : ℝ≥0) (x : FiniteMeasure K), e (c • x) = c • e x) :
    IsCompactConvexClosedBoundary ℝ≥0 (e '' probSimplex K) :=
  isCompactConvexClosedBoundary_probSimplex.image e hcont hinj hadd hsmul

/-- Under the same identification, the extreme boundary of the trace simplex is
the image of `K` under `x ↦ e (δₓ)`. -/
theorem extremePoints_probSimplex_image
    [TopologicalSpace K] [T2Space K] [SecondCountableTopology K] [BorelSpace K]
    {V : Type*} [AddCommMonoid V] [SMul ℝ≥0 V]
    (e : FiniteMeasure K → V) (hinj : Function.Injective e)
    (hadd : ∀ x y : FiniteMeasure K, e (x + y) = e x + e y)
    (hsmul : ∀ (c : ℝ≥0) (x : FiniteMeasure K), e (c • x) = c • e x) :
    (e '' probSimplex K).extremePoints ℝ≥0 = Set.range (fun x : K => e (diracFM x)) := by
  rw [extremePoints_image_of_linear e hinj hadd hsmul (probSimplex K), extremePoints_probSimplex]
  exact (Set.range_comp' e diracFM).symm

end

end STW22
end GroupApproximation
