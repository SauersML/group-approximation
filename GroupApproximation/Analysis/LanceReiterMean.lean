import GroupApproximation.Algebra.AmenableMean
import Mathlib.Order.Filter.AtTopBot.Prod
import Mathlib.Analysis.SpecificLimits.Basic

/-!
# Reiter's condition implies an invariant mean

## Where this sits in the Lance lane

`NuclearityAmenability.reducedGroupCStar_not_nuclear_of_lance` consumes
Lance's theorem — nuclearity of `C*_λ(G)` forces an invariant mean on `G` —
as an explicit hypothesis, because at the pinned Mathlib revision neither
side of that implication had any formal support.  The standard proof
(Brown–Ozawa, Theorem 2.6.8) factors as

```
  CPAP of C*_λ(G)
    ⟹ (Stinespring + the canonical trace)
  positive-definite functions on G tending to 1 pointwise
    ⟹ (coefficients, |ξ|²)                        [LancePositiveDefinite]
  Reiter's condition: almost-invariant ℓ¹ densities
    ⟹ (weak-* limit along an ultrafilter)          [THIS FILE]
  an invariant mean on bounded functions.
```

This module formalizes the **last arrow in full**: a group satisfying
Reiter's condition — for every finite set and tolerance there is a finitely
supported probability density that left translation moves by at most the
tolerance in `ℓ¹` — carries an invariant mean in the repository's own sense
(`Amenability.FunctionMean`, hence `Amenability.HasInvariantMean`).

The construction is the classical weak-* compactness argument, executed with
the same ultrafilter device as `Amenability.isAmenable_of_directed`: the
density attached to the index `(F, n)` (translation controlled on `F` up to
`1/(n+1)`) gives a finitely supported average of any bounded function; the
averages of a fixed bounded function form a bounded family of reals, so they
converge along a fixed ultrafilter refining `atTop` on `Finset G × ℕ`; the
limit inherits additivity, positivity and normalization pointwise, and
inherits *invariance* because the translation defect of the average is
bounded by `C/(n+1)` eventually, which tends to `0` along `atTop` and hence
along the ultrafilter.

## What is and is not claimed

* `ReiterCondition` here is stated for finitely supported densities, which
  is the form the positive-definite lane produces; no `ℓ¹`-space, no
  topology on densities and no net convergence apparatus is introduced.
* This is one arrow of the Lance chain and nothing more.  Nothing here
  mentions `C*`-algebras, nuclearity, or the CPAP.

## Manuscript status

Infrastructure for the `RE.05` row.  `RE.05` remains conditional on Lance
(`MISMATCH`/`literature-input` in the ledger): the arrows from the CPAP down
to `ReiterCondition` are not all formalized, and nothing here or in the
companion modules discharges the `lance` hypothesis of
`reducedGroupCStar_not_nuclear_of_lance`.  See `LanceReduction.lean` for the
exact residual statement.
-/

namespace GroupApproximation
namespace LanceAmenability

open Amenability Filter Topology

universe u

variable {G : Type u} [Group G]

/-! ## Finitely supported densities: mass, translation, `ℓ¹` size -/

/-- The total mass of a finitely supported real function. -/
def totalMass (μ : G →₀ ℝ) : ℝ := ∑ x ∈ μ.support, μ x

/-- The `ℓ¹` norm of a finitely supported real function. -/
def l1Norm (ν : G →₀ ℝ) : ℝ := ∑ x ∈ ν.support, |ν x|

/-- The left translate of a finitely supported function:
`(leftTranslate g μ) x = μ (g⁻¹ * x)`. -/
def leftTranslate (g : G) (μ : G →₀ ℝ) : G →₀ ℝ :=
  Finsupp.equivMapDomain (Equiv.mulLeft g) μ

@[simp] theorem leftTranslate_apply (g : G) (μ : G →₀ ℝ) (x : G) :
    leftTranslate g μ x = μ (g⁻¹ * x) := by
  show μ ((Equiv.mulLeft g).symm x) = μ (g⁻¹ * x)
  rw [Equiv.mulLeft_symm_apply]

/-- On nonnegative densities the `ℓ¹` norm is the total mass. -/
theorem l1Norm_eq_totalMass {μ : G →₀ ℝ} (hμ : ∀ x, 0 ≤ μ x) :
    l1Norm μ = totalMass μ := by
  refine Finset.sum_congr rfl fun x _ ↦ ?_
  exact abs_of_nonneg (hμ x)

/-- Translation preserves the total mass. -/
theorem totalMass_leftTranslate (g : G) (μ : G →₀ ℝ) :
    totalMass (leftTranslate g μ) = totalMass μ := by
  show (Finsupp.equivMapDomain (Equiv.mulLeft g) μ).sum (fun _ v ↦ v)
      = μ.sum (fun _ v ↦ v)
  rw [Finsupp.sum_equivMapDomain]

/-! ## Reiter's condition -/

/-- **Reiter's condition** for a discrete group, in the finitely supported
form: for every finite set of group elements and every positive tolerance
there is a finitely supported probability density whose left translates by
the given elements are within the tolerance in `ℓ¹`. -/
def ReiterCondition (G : Type u) [Group G] : Prop :=
  ∀ (F : Finset G) (ε : ℝ), 0 < ε →
    ∃ μ : G →₀ ℝ, (∀ x, 0 ≤ μ x) ∧ totalMass μ = 1 ∧
      ∀ g ∈ F, l1Norm (leftTranslate g μ - μ) ≤ ε

/-! ## Weighted averages of bounded functions -/

/-- The average of a function against a finitely supported weight. -/
def weightedAvg (μ : G →₀ ℝ) (f : G → ℝ) : ℝ := ∑ x ∈ μ.support, μ x * f x

/-- The weighted average is additive in the weight, for weights differing by
subtraction; this is `Finsupp.sum_sub_index` read through the definition. -/
theorem weightedAvg_sub (ν ν' : G →₀ ℝ) (f : G → ℝ) :
    weightedAvg (ν - ν') f = weightedAvg ν f - weightedAvg ν' f := by
  show (ν - ν').sum (fun x v ↦ v * f x)
      = ν.sum (fun x v ↦ v * f x) - ν'.sum (fun x v ↦ v * f x)
  exact Finsupp.sum_sub_index fun a b₁ b₂ ↦ sub_mul b₁ b₂ (f a)

/-- The weighted average is additive in the function. -/
theorem weightedAvg_add_fun (μ : G →₀ ℝ) (f h : G → ℝ) :
    weightedAvg μ (f + h) = weightedAvg μ f + weightedAvg μ h := by
  show ∑ x ∈ μ.support, μ x * (f x + h x)
      = (∑ x ∈ μ.support, μ x * f x) + ∑ x ∈ μ.support, μ x * h x
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun x _ ↦ ?_
  rw [mul_add]

/-- The weighted average of a constant is the mass times the constant. -/
theorem weightedAvg_const (μ : G →₀ ℝ) (c : ℝ) :
    weightedAvg μ (fun _ ↦ c) = totalMass μ * c := by
  show ∑ x ∈ μ.support, μ x * c = (∑ x ∈ μ.support, μ x) * c
  rw [Finset.sum_mul]

/-- Nonnegative weight, nonnegative function: nonnegative average. -/
theorem weightedAvg_nonneg {μ : G →₀ ℝ} (hμ : ∀ x, 0 ≤ μ x) {f : G → ℝ}
    (hf : ∀ x, 0 ≤ f x) : 0 ≤ weightedAvg μ f :=
  Finset.sum_nonneg fun x _ ↦ mul_nonneg (hμ x) (hf x)

/-- The basic `ℓ¹`–`ℓ^∞` estimate for weighted averages. -/
theorem abs_weightedAvg_le (ν : G →₀ ℝ) {f : G → ℝ} {C : ℝ}
    (hC : ∀ x, |f x| ≤ C) : |weightedAvg ν f| ≤ l1Norm ν * C := by
  calc |∑ x ∈ ν.support, ν x * f x|
      ≤ ∑ x ∈ ν.support, |ν x * f x| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ x ∈ ν.support, |ν x| * C := by
        refine Finset.sum_le_sum fun x _ ↦ ?_
        rw [abs_mul]
        exact mul_le_mul_of_nonneg_left (hC x) (abs_nonneg _)
    _ = l1Norm ν * C := by rw [l1Norm, Finset.sum_mul]

/-- Averages of a bounded function against probability densities are bounded
by the bound of the function. -/
theorem abs_weightedAvg_le_of_prob {μ : G →₀ ℝ} (hμ : ∀ x, 0 ≤ μ x)
    (hmass : totalMass μ = 1) {f : G → ℝ} {C : ℝ} (hC : ∀ x, |f x| ≤ C) :
    |weightedAvg μ f| ≤ C := by
  have h1 := abs_weightedAvg_le μ hC
  rwa [l1Norm_eq_totalMass hμ, hmass, one_mul] at h1

/-- **The translation identity**: averaging `x ↦ f (g * x)` against `μ` is
averaging `f` against the left translate of `μ`. -/
theorem weightedAvg_comp_left (g : G) (μ : G →₀ ℝ) (f : G → ℝ) :
    weightedAvg μ (fun x ↦ f (g * x)) = weightedAvg (leftTranslate g μ) f := by
  show μ.sum (fun x v ↦ v * f (g * x))
      = (Finsupp.equivMapDomain (Equiv.mulLeft g) μ).sum (fun x v ↦ v * f x)
  rw [Finsupp.sum_equivMapDomain]
  -- after the reindexing both sides are the same sum, up to unfolding the
  -- coercion of `Equiv.mulLeft`
  simp only [Equiv.coe_mulLeft]

/-! ## The index, its ultrafilter, and the chosen densities -/

section Construction

variable [DecidableEq G]

/-- The Reiter index: a finite set of translations to control, and the
reciprocal tolerance. -/
abbrev ReiterIndex (G : Type u) [Group G] [DecidableEq G] : Type u :=
  Finset G × ℕ

/-- The fixed ultrafilter refining the eventually-large filter on the
index. -/
noncomputable def reiterUltra (G : Type u) [Group G] [DecidableEq G] :
    Ultrafilter (ReiterIndex G) :=
  indexUltrafilter (ReiterIndex G) ⟨(∅, 0)⟩

theorem reiterUltra_le_atTop :
    (reiterUltra G : Filter (ReiterIndex G)) ≤ Filter.atTop :=
  indexUltrafilter_le ⟨(∅, 0)⟩

variable (hR : ReiterCondition G)

/-- The tolerance attached to an index. -/
def tol (i : ReiterIndex G) : ℝ := 1 / ((i.2 : ℝ) + 1)

theorem tol_pos (i : ReiterIndex G) : 0 < tol i := by
  have h1 : (0 : ℝ) < (i.2 : ℝ) + 1 := by positivity
  exact div_pos one_pos h1

/-- The tolerances tend to zero along the eventually-large filter. -/
theorem tendsto_tol_atTop :
    Tendsto (tol (G := G)) Filter.atTop (nhds 0) := by
  have hsnd : Tendsto (fun i : ReiterIndex G ↦ i.2)
      (Filter.atTop : Filter (ReiterIndex G)) Filter.atTop := by
    rw [← Filter.prod_atTop_atTop_eq]
    exact Filter.tendsto_snd
  have hnat : Tendsto (fun n : ℕ ↦ 1 / ((n : ℝ) + 1)) Filter.atTop (nhds 0) :=
    tendsto_one_div_add_atTop_nhds_zero_nat
  exact hnat.comp hsnd

/-- The chosen Reiter density at an index. -/
noncomputable def reiterDensity (i : ReiterIndex G) : G →₀ ℝ :=
  (hR i.1 (tol i) (tol_pos i)).choose

theorem reiterDensity_nonneg (i : ReiterIndex G) :
    ∀ x, 0 ≤ reiterDensity hR i x :=
  (hR i.1 (tol i) (tol_pos i)).choose_spec.1

theorem reiterDensity_mass (i : ReiterIndex G) :
    totalMass (reiterDensity hR i) = 1 :=
  (hR i.1 (tol i) (tol_pos i)).choose_spec.2.1

theorem reiterDensity_close (i : ReiterIndex G) :
    ∀ g ∈ i.1, l1Norm (leftTranslate g (reiterDensity hR i)
      - reiterDensity hR i) ≤ tol i :=
  (hR i.1 (tol i) (tol_pos i)).choose_spec.2.2

/-! ## The limit along the ultrafilter -/

/-- The net of averages of a bounded function converges along the fixed
ultrafilter: the averages live in `[-C, C]`. -/
theorem reiterTendsto {f : G → ℝ} (hf : IsBddFun f) :
    ∃ L : ℝ, Tendsto (fun i ↦ weightedAvg (reiterDensity hR i) f)
      (reiterUltra G) (nhds L) := by
  classical
  set C := Classical.choose hf with hCdef
  have hC : ∀ x, |f x| ≤ C := Classical.choose_spec hf
  obtain ⟨L, _, hL⟩ := exists_ultrafilter_tendsto_Icc (reiterUltra G)
    (fun i ↦ weightedAvg (reiterDensity hR i) f) (a := -C) (b := C)
    (fun i ↦ abs_le.mp (abs_weightedAvg_le_of_prob
      (reiterDensity_nonneg hR i) (reiterDensity_mass hR i) hC))
  exact ⟨L, hL⟩

/-- The limit average of a bounded function. -/
noncomputable def reiterEvalOf {f : G → ℝ} (hf : IsBddFun f) : ℝ :=
  (reiterTendsto hR hf).choose

theorem reiterEvalOf_tendsto {f : G → ℝ} (hf : IsBddFun f) :
    Tendsto (fun i ↦ weightedAvg (reiterDensity hR i) f)
      (reiterUltra G) (nhds (reiterEvalOf hR hf)) :=
  (reiterTendsto hR hf).choose_spec

open Classical in
/-- The limit average, extended by zero to unbounded functions. -/
noncomputable def reiterEval (f : G → ℝ) : ℝ :=
  if h : IsBddFun f then reiterEvalOf hR h else 0

theorem reiterEval_tendsto {f : G → ℝ} (hf : IsBddFun f) :
    Tendsto (fun i ↦ weightedAvg (reiterDensity hR i) f)
      (reiterUltra G) (nhds (reiterEval hR f)) := by
  classical
  simp only [reiterEval, dif_pos hf]
  exact reiterEvalOf_tendsto hR hf

/-! ## Invariance of the limit -/

/-- **The invariance estimate.**  For a fixed `g` and a bounded `f`, the
average of the left composite eventually differs from the average of `f` by
at most `C` times the tolerance, because the translation defect of the
density is controlled once `g` enters the finite set of the index. -/
theorem eventually_abs_diff_le {g : G} {f : G → ℝ} {C : ℝ}
    (hC : ∀ x, |f x| ≤ C) :
    ∀ᶠ i in (Filter.atTop : Filter (ReiterIndex G)),
      |weightedAvg (reiterDensity hR i) (fun x ↦ f (g * x))
        - weightedAvg (reiterDensity hR i) f| ≤ C * tol i := by
  have hCnn : 0 ≤ C := le_trans (abs_nonneg _) (hC 1)
  refine Filter.mem_of_superset
    (Filter.eventually_ge_atTop ((({g} : Finset G), 0) : ReiterIndex G)) ?_
  intro i hi
  have hgF : g ∈ i.1 := by
    have h1 : ({g} : Finset G) ≤ i.1 := (Prod.mk_le_mk.mp hi).1
    exact Finset.singleton_subset_iff.mp h1
  have hclose : l1Norm (leftTranslate g (reiterDensity hR i)
      - reiterDensity hR i) ≤ tol i := reiterDensity_close hR i g hgF
  show |weightedAvg (reiterDensity hR i) (fun x ↦ f (g * x))
      - weightedAvg (reiterDensity hR i) f| ≤ C * tol i
  rw [weightedAvg_comp_left, ← weightedAvg_sub]
  calc |weightedAvg (leftTranslate g (reiterDensity hR i)
        - reiterDensity hR i) f|
      ≤ l1Norm (leftTranslate g (reiterDensity hR i)
          - reiterDensity hR i) * C := abs_weightedAvg_le _ hC
    _ ≤ tol i * C := by
        refine mul_le_mul_of_nonneg_right hclose hCnn
    _ = C * tol i := mul_comm _ _

/-- The difference of the two nets of averages tends to zero along the
ultrafilter. -/
theorem tendsto_diff_zero {g : G} {f : G → ℝ} (hf : IsBddFun f) :
    Tendsto (fun i ↦ weightedAvg (reiterDensity hR i) (fun x ↦ f (g * x))
      - weightedAvg (reiterDensity hR i) f)
      (reiterUltra G) (nhds 0) := by
  classical
  obtain ⟨C, hC⟩ := hf
  have hCnn : 0 ≤ C := le_trans (abs_nonneg _) (hC 1)
  have hb : Tendsto (fun i : ReiterIndex G ↦ C * tol i)
      (Filter.atTop : Filter (ReiterIndex G)) (nhds 0) := by
    have h1 := (tendsto_tol_atTop (G := G)).const_mul C
    rwa [mul_zero] at h1
  have hbu : Tendsto (fun i : ReiterIndex G ↦ C * tol i)
      (reiterUltra G) (nhds 0) := hb.mono_left reiterUltra_le_atTop
  have hbu' : Tendsto (fun i : ReiterIndex G ↦ -(C * tol i))
      (reiterUltra G) (nhds 0) := by
    have h1 := hbu.neg
    rwa [neg_zero] at h1
  have hev : ∀ᶠ i in (reiterUltra G : Filter (ReiterIndex G)),
      |weightedAvg (reiterDensity hR i) (fun x ↦ f (g * x))
        - weightedAvg (reiterDensity hR i) f| ≤ C * tol i :=
    reiterUltra_le_atTop (eventually_abs_diff_le hR hC)
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' hbu' hbu ?_ ?_
  · exact hev.mono fun i hi ↦ (abs_le.mp hi).1
  · exact hev.mono fun i hi ↦ (abs_le.mp hi).2

end Construction

/-! ## The invariant mean -/

/-- **Reiter's condition yields an invariant mean.**  The mean of a bounded
function is the ultrafilter limit of its averages against the chosen Reiter
densities; additivity, positivity and normalization pass through the limit
pointwise, and left invariance is `tendsto_diff_zero`. -/
theorem hasInvariantMean_of_reiter (hR : ReiterCondition G) :
    HasInvariantMean G := by
  classical
  refine ⟨{ eval := reiterEval hR
            eval_add := ?_
            eval_nonneg := ?_
            eval_const := ?_
            eval_invariant := ?_ }⟩
  · -- additivity
    intro f g hf hg
    refine tendsto_nhds_unique (reiterEval_tendsto hR (hf.add hg)) ?_
    have hsplit : (fun i ↦ weightedAvg (reiterDensity hR i) (f + g))
        = fun i ↦ weightedAvg (reiterDensity hR i) f
          + weightedAvg (reiterDensity hR i) g := by
      funext i
      exact weightedAvg_add_fun _ f g
    rw [hsplit]
    exact (reiterEval_tendsto hR hf).add (reiterEval_tendsto hR hg)
  · -- positivity
    intro f hf hpos
    refine ge_of_tendsto (reiterEval_tendsto hR hf)
      (Filter.Eventually.of_forall fun i ↦ ?_)
    exact weightedAvg_nonneg (reiterDensity_nonneg hR i) hpos
  · -- normalization
    intro c
    refine tendsto_nhds_unique (reiterEval_tendsto hR (IsBddFun.const c)) ?_
    have hconst : (fun i ↦ weightedAvg (reiterDensity hR i) (fun _ ↦ c))
        = fun _ ↦ c := by
      funext i
      rw [weightedAvg_const, reiterDensity_mass hR i, one_mul]
    rw [hconst]
    exact tendsto_const_nhds
  · -- invariance
    intro g f hf
    have hfg : IsBddFun (fun x ↦ f (g * x)) := by
      obtain ⟨C, hC⟩ := hf
      exact ⟨C, fun x ↦ hC _⟩
    refine tendsto_nhds_unique (reiterEval_tendsto hR hfg) ?_
    have hsum : (fun i ↦ weightedAvg (reiterDensity hR i) (fun x ↦ f (g * x)))
        = fun i ↦ weightedAvg (reiterDensity hR i) f
          + (weightedAvg (reiterDensity hR i) (fun x ↦ f (g * x))
            - weightedAvg (reiterDensity hR i) f) := by
      funext i
      ring
    rw [hsum]
    have h1 := (reiterEval_tendsto hR hf).add (tendsto_diff_zero hR (g := g) hf)
    rwa [add_zero] at h1

end LanceAmenability
end GroupApproximation
