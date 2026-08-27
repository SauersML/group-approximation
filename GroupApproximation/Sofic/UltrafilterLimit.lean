import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Analysis.RCLike.Basic
import Mathlib.Order.Filter.Ultrafilter.Basic

/-!
# `lim_ω` for a bounded family, along an arbitrary ultrafilter

The proof of `thm:kazhdan-transport` in `non_mf_groups_exist.tex` fixes a free
ultrafilter `ω` on `ℕ` and then writes `lim_ω` for scalars: faithfulness of the
action of `B_ω` on `K_ω` is stated as `lim_ω ‖A_n‖ = δ > 0`, and the inner
product of `K_ω` is `lim_ω` of the coordinate inner products.

`Kazhdan/UltralimitGeometry.lean` already has an ultralimit, but it is the
*hyperreal* one: `Hyperreal.ofSeq` is the germ along Mathlib's `hyperfilter`,
one fixed ultrafilter.  The manuscript's `ω` is chosen after the fact to
contain a prescribed infinite set of bad indices — that is the step
`exists_freeUltrafilter_mem` supplies — so the limit has to be available along
*every* ultrafilter, not along one distinguished one.

Everything here is the standard compactness argument: a family with values in
a closed ball of a proper space pushes an ultrafilter to one on a compact set,
which converges; uniqueness of limits in a Hausdorff space then makes the limit
a function of the family, and each algebraic identity is `tendsto_nhds_unique`
applied to a continuity lemma.
-/

namespace GroupApproximation
namespace UltrafilterLimit

open Filter Topology

/-! ## Choosing the ultrafilter -/

/-- **The manuscript's choice of `ω`.**  Given an infinite set `I` of bad
indices there is a free ultrafilter containing it: free because it refines the
cofinite filter, which is what lets every cofinite statement be used along `ω`
and is exactly the manuscript's replacement of "for all large `n`" by "on a set
belonging to `ω`". -/
theorem exists_freeUltrafilter_mem {I : Set ℕ} (hI : I.Infinite) :
    ∃ ω : Ultrafilter ℕ, I ∈ ω ∧ (ω : Filter ℕ) ≤ cofinite := by
  haveI hne : (cofinite ⊓ 𝓟 I : Filter ℕ).NeBot := by
    refine Filter.inf_principal_neBot_iff.mpr fun {t} ht ↦ ?_
    by_contra hemp
    have hsub : I ⊆ tᶜ := by
      intro x hx
      by_contra hxt
      exact hemp ⟨x, not_not.mp hxt, hx⟩
    exact hI ((Filter.mem_cofinite.mp ht).subset hsub)
  refine ⟨Ultrafilter.of (cofinite ⊓ 𝓟 I), ?_, ?_⟩
  · exact Ultrafilter.of_le _ (mem_inf_of_right (mem_principal_self I))
  · exact (Ultrafilter.of_le _).trans inf_le_left

/-! ## The limit itself -/

variable {E : Type*} [NormedAddCommGroup E]

/-- A norm-bounded family converges along every ultrafilter. -/
theorem exists_tendsto_of_bounded [ProperSpace E] (ω : Ultrafilter ℕ)
    {f : ℕ → E} {C : ℝ}
    (hf : ∀ n, ‖f n‖ ≤ C) :
    ∃ L : E, Tendsto f (ω : Filter ℕ) (𝓝 L) := by
  have hmap : ((ω.map f : Ultrafilter E) : Filter E)
      ≤ 𝓟 (Metric.closedBall (0 : E) C) := by
    rw [Ultrafilter.coe_map, le_principal_iff]
    refine Filter.mem_map.mpr (Filter.univ_mem' fun n ↦ ?_)
    simpa [Metric.mem_closedBall, dist_zero_right] using hf n
  obtain ⟨L, -, hL⟩ :=
    (isCompact_closedBall (0 : E) C).ultrafilter_le_nhds (ω.map f) hmap
  refine ⟨L, ?_⟩
  rwa [Tendsto, ← Ultrafilter.coe_map]

open scoped Classical in
/-- `lim_ω f`.  The junk value `0` is taken on families that do not converge,
which the manuscript never forms: every use below carries the bound. -/
noncomputable def ulim (ω : Ultrafilter ℕ) (f : ℕ → E) : E :=
  if h : ∃ L : E, Tendsto f (ω : Filter ℕ) (𝓝 L) then h.choose else 0

theorem tendsto_ulim {ω : Ultrafilter ℕ} {f : ℕ → E}
    (h : ∃ L : E, Tendsto f (ω : Filter ℕ) (𝓝 L)) :
    Tendsto f (ω : Filter ℕ) (𝓝 (ulim ω f)) := by
  rw [ulim, dif_pos h]
  exact h.choose_spec

theorem tendsto_ulim_of_bounded [ProperSpace E] {ω : Ultrafilter ℕ}
    {f : ℕ → E} {C : ℝ} (hf : ∀ n, ‖f n‖ ≤ C) :
    Tendsto f (ω : Filter ℕ) (𝓝 (ulim ω f)) :=
  tendsto_ulim (exists_tendsto_of_bounded ω hf)

/-- The limit is determined by any witness: uniqueness in a Hausdorff space. -/
theorem ulim_eq {ω : Ultrafilter ℕ} {f : ℕ → E} {L : E}
    (h : Tendsto f (ω : Filter ℕ) (𝓝 L)) : ulim ω f = L :=
  tendsto_nhds_unique (tendsto_ulim ⟨L, h⟩) h

@[simp] theorem ulim_const (ω : Ultrafilter ℕ) (c : E) :
    ulim ω (fun _ ↦ c) = c :=
  ulim_eq tendsto_const_nhds

/-- Families agreeing on a set of `ω` have the same limit.  This is where the
manuscript's "on a set belonging to `ω`" enters the scalar calculus. -/
theorem ulim_congr {ω : Ultrafilter ℕ} {f g : ℕ → E}
    (h : ∀ᶠ n in (ω : Filter ℕ), f n = g n)
    (hf : ∃ L : E, Tendsto f (ω : Filter ℕ) (𝓝 L)) :
    ulim ω f = ulim ω g :=
  (ulim_eq ((tendsto_ulim hf).congr' h)).symm

section Algebra

variable {ω : Ultrafilter ℕ} {f g : ℕ → E}

theorem ulim_add (hf : ∃ L : E, Tendsto f (ω : Filter ℕ) (𝓝 L))
    (hg : ∃ L : E, Tendsto g (ω : Filter ℕ) (𝓝 L)) :
    ulim ω (fun n ↦ f n + g n) = ulim ω f + ulim ω g :=
  ulim_eq ((tendsto_ulim hf).add (tendsto_ulim hg))

theorem ulim_neg (hf : ∃ L : E, Tendsto f (ω : Filter ℕ) (𝓝 L)) :
    ulim ω (fun n ↦ -f n) = -ulim ω f :=
  ulim_eq (tendsto_ulim hf).neg

theorem ulim_sub (hf : ∃ L : E, Tendsto f (ω : Filter ℕ) (𝓝 L))
    (hg : ∃ L : E, Tendsto g (ω : Filter ℕ) (𝓝 L)) :
    ulim ω (fun n ↦ f n - g n) = ulim ω f - ulim ω g :=
  ulim_eq ((tendsto_ulim hf).sub (tendsto_ulim hg))

end Algebra

/-! ## Complex scalars, for the inner product of `K_ω` -/

section ComplexScalars

variable {ω : Ultrafilter ℕ} {f : ℕ → ℂ}

theorem ulim_const_mul (c : ℂ)
    (hf : ∃ L : ℂ, Tendsto f (ω : Filter ℕ) (𝓝 L)) :
    ulim ω (fun n ↦ c * f n) = c * ulim ω f :=
  ulim_eq ((tendsto_ulim hf).const_mul c)

theorem ulim_conj (hf : ∃ L : ℂ, Tendsto f (ω : Filter ℕ) (𝓝 L)) :
    ulim ω (fun n ↦ (starRingEnd ℂ) (f n))
      = (starRingEnd ℂ) (ulim ω f) := by
  have hstar : Continuous (fun z : ℂ ↦ (starRingEnd ℂ) z) := continuous_star
  exact ulim_eq ((hstar.tendsto _).comp (tendsto_ulim hf))

end ComplexScalars

/-! ## Real scalars, for masses and norms -/

section Real

variable {ω : Ultrafilter ℕ} {f : ℕ → ℝ}

/-- A lower bound holding on a set of `ω` passes to the limit. -/
theorem le_ulim (hf : ∃ L : ℝ, Tendsto f (ω : Filter ℕ) (𝓝 L)) {c : ℝ}
    (h : ∀ᶠ n in (ω : Filter ℕ), c ≤ f n) : c ≤ ulim ω f :=
  ge_of_tendsto (tendsto_ulim hf) h

theorem ulim_nonneg (hf : ∃ L : ℝ, Tendsto f (ω : Filter ℕ) (𝓝 L))
    (h : ∀ n, 0 ≤ f n) : 0 ≤ ulim ω f :=
  le_ulim hf (Eventually.of_forall h)

/-- An upper bound holding on a set of `ω` passes to the limit. -/
theorem ulim_le (hf : ∃ L : ℝ, Tendsto f (ω : Filter ℕ) (𝓝 L)) {c : ℝ}
    (h : ∀ᶠ n in (ω : Filter ℕ), f n ≤ c) : ulim ω f ≤ c :=
  le_of_tendsto (tendsto_ulim hf) h

/-- **The `ε`-form used at every call site.**  A limit below `c` forces the
family below `c` on a set of `ω`; this is the direction that turns a statement
about `lim_ω` back into the manuscript's "on a set belonging to `ω`". -/
theorem eventually_lt_of_ulim_lt (hf : ∃ L : ℝ, Tendsto f (ω : Filter ℕ) (𝓝 L))
    {c : ℝ} (h : ulim ω f < c) : ∀ᶠ n in (ω : Filter ℕ), f n < c :=
  (tendsto_ulim hf).eventually_lt_const h

/-- A family whose limit vanishes is small on a set of `ω`. -/
theorem eventually_lt_of_ulim_eq_zero
    (hf : ∃ L : ℝ, Tendsto f (ω : Filter ℕ) (𝓝 L)) (h : ulim ω f = 0)
    {ε : ℝ} (hε : 0 < ε) : ∀ᶠ n in (ω : Filter ℕ), f n < ε :=
  eventually_lt_of_ulim_lt hf (by rw [h]; exact hε)

end Real

end UltrafilterLimit
end GroupApproximation
