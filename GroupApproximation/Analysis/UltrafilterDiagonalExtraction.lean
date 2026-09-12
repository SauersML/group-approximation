import Mathlib.Order.Filter.AtTopBot.Basic
import Mathlib.Order.Filter.Cofinite
import Mathlib.Order.Filter.Finite
import Mathlib.Order.Filter.Ultrafilter.Basic
import Mathlib.Topology.MetricSpace.Pseudo.Defs
import Mathlib.Algebra.Order.Archimedean.Basic
import Mathlib.Analysis.Complex.Basic
import Mathlib.Data.Countable.Defs
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# From an ultrafilter limit to a subsequential limit

Several places in this development produce convergence **along a free
ultrafilter** `ω` on `ℕ` -- an ultralimit is available for *every* bounded
family, which is exactly why the ultraproduct route is usable at all -- while
the definitions that must be satisfied downstream (MF, operator-MF, the
Shulman trace conditions) ask for an ordinary `Filter.atTop` limit of a
sequence.  The two are not the same statement, and the gap is real: an
`ω`-limit says nothing about any particular tail.

What closes it is a subsequence.  This file proves the general extraction, with
nothing about traces, matrices or C\*-algebras in it:

> Given countably many sequences `F i : ℕ → X` in a pseudometric space, each
> converging along a free ultrafilter `ω` to `L i`, there is a single strictly
> monotone `φ : ℕ → ℕ` along which *every* `F i` converges to `L i` in the
> ordinary sense.

The countability of the index set is what makes one `φ` serve all `i` at once;
for an uncountable family the statement is false.

## The argument, and what Mathlib already supplies

For each tolerance level `k` the set of stages `n` at which the first `k + 1`
sequences are all within `1 / (k + 1)` of their limits is a finite
intersection of `ω`-large sets (`Filter.eventually_all_finset`), hence
`ω`-large.  A free ultrafilter refines the cofinite filter, which on `ℕ` is
`atTop` (`Nat.cofinite_eq_atTop`), so an `ω`-large set is `atTop`-frequent --
this is the only place freeness is used, and it is used exactly once.
`Filter.extraction_forall_of_frequently` then performs the diagonal choice and
hands back the strictly monotone `φ`.  The file is therefore assembly: no
recursion is defined here.

## Hypotheses deliberately absent

The informal statement of this lemma is usually made for *bounded* families,
because boundedness is how one gets the ultrafilter limits in the first place.
Once the limits `L i` are hypotheses there is nothing left for boundedness to
do, so it is not assumed: the theorems below apply verbatim to unbounded
families that happen to converge along `ω`.
-/

namespace GroupApproximation
namespace UltrafilterDiagonalExtraction

open Filter Topology

/-! ## The extraction -/

/-- **Diagonal extraction from an ultrafilter limit.**  Let `ω` be a free
ultrafilter on `ℕ` (`NeBot` comes with `Ultrafilter`; `≤ cofinite` is
non-principality).  If each member of a countable family of sequences `F i`
converges to `L i` along `ω`, then a single strictly monotone `φ` makes every
`F i ∘ φ` converge to `L i` along `atTop`.

No boundedness is assumed -- see the module docstring. -/
theorem exists_strictMono_tendsto_atTop {X : Type*} [PseudoMetricSpace X]
    {ω : Ultrafilter ℕ} (hω : (ω : Filter ℕ) ≤ cofinite)
    (F : ℕ → ℕ → X) (L : ℕ → X)
    (hF : ∀ i, Tendsto (F i) (ω : Filter ℕ) (𝓝 (L i))) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧
      ∀ i, Tendsto (fun k ↦ F i (φ k)) atTop (𝓝 (L i)) := by
  -- Freeness, in the only form the argument needs.
  have hωtop : (ω : Filter ℕ) ≤ atTop := hω.trans_eq Nat.cofinite_eq_atTop
  -- At tolerance level `k`: the first `k + 1` sequences are simultaneously
  -- within `1 / (k + 1)` at `ω`-many stages, hence at arbitrarily late ones.
  have hfreq : ∀ k : ℕ, ∃ᶠ n in atTop,
      ∀ i ∈ Finset.range (k + 1), dist (F i n) (L i) < 1 / ((k : ℝ) + 1) := by
    intro k
    have hpos : (0 : ℝ) < 1 / ((k : ℝ) + 1) := by positivity
    have hall : ∀ i ∈ Finset.range (k + 1),
        ∀ᶠ n in (ω : Filter ℕ), dist (F i n) (L i) < 1 / ((k : ℝ) + 1) :=
      fun i _ ↦ Metric.tendsto_nhds.mp (hF i) _ hpos
    have hev : ∀ᶠ n in (ω : Filter ℕ),
        ∀ i ∈ Finset.range (k + 1), dist (F i n) (L i) < 1 / ((k : ℝ) + 1) :=
      (Filter.eventually_all_finset (Finset.range (k + 1))).mpr hall
    exact hev.frequently.filter_mono hωtop
  obtain ⟨φ, hmono, hφ⟩ := extraction_forall_of_frequently hfreq
  refine ⟨φ, hmono, fun i ↦ Metric.tendsto_atTop.mpr fun ε hε ↦ ?_⟩
  obtain ⟨N, hN⟩ := exists_nat_one_div_lt hε
  refine ⟨max i N, fun k hk ↦ ?_⟩
  show dist (F i (φ k)) (L i) < ε
  have hik : i < k + 1 := Nat.lt_succ_of_le ((le_max_left i N).trans hk)
  have hNk : (N : ℝ) + 1 ≤ (k : ℝ) + 1 := by
    have hle : (N : ℝ) ≤ (k : ℝ) := Nat.cast_le.mpr ((le_max_right i N).trans hk)
    linarith
  have hposN : (0 : ℝ) < (N : ℝ) + 1 := by positivity
  have h1 : dist (F i (φ k)) (L i) < 1 / ((k : ℝ) + 1) :=
    hφ k i (Finset.mem_range.mpr hik)
  have h2 : 1 / ((k : ℝ) + 1) ≤ 1 / ((N : ℝ) + 1) := one_div_le_one_div_of_le hposN hNk
  linarith

/-- The same extraction for a family indexed by an arbitrary countable type.
Reindexing along a surjection `ℕ → ι` is all that separates this from
`exists_strictMono_tendsto_atTop`; countability is exactly the hypothesis that
makes one subsequence serve every index. -/
theorem exists_strictMono_tendsto_atTop_countable {ι : Type*} [Countable ι]
    {X : Type*} [PseudoMetricSpace X]
    {ω : Ultrafilter ℕ} (hω : (ω : Filter ℕ) ≤ cofinite)
    (F : ι → ℕ → X) (L : ι → X)
    (hF : ∀ i, Tendsto (F i) (ω : Filter ℕ) (𝓝 (L i))) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧
      ∀ i, Tendsto (fun k ↦ F i (φ k)) atTop (𝓝 (L i)) := by
  rcases isEmpty_or_nonempty ι with hι | _
  · exact ⟨id, strictMono_id, fun i ↦ (hι.false i).elim⟩
  obtain ⟨e, he⟩ := exists_surjective_nat ι
  obtain ⟨φ, hmono, hφ⟩ :=
    exists_strictMono_tendsto_atTop hω (fun j ↦ F (e j)) (fun j ↦ L (e j))
      (fun j ↦ hF (e j))
  refine ⟨φ, hmono, fun i ↦ ?_⟩
  obtain ⟨j, hj⟩ := he i
  have := hφ j
  rwa [hj] at this

/-! ## The scalar cases

`ℝ` and `ℂ` are pseudometric spaces, so these are instantiations.  The complex
one is what the trace comparisons need: `|τ(a) - tr (φ n a)|` is a complex
modulus. -/

/-- The real-valued case of `exists_strictMono_tendsto_atTop`. -/
theorem exists_strictMono_tendsto_atTop_real
    {ω : Ultrafilter ℕ} (hω : (ω : Filter ℕ) ≤ cofinite)
    (F : ℕ → ℕ → ℝ) (L : ℕ → ℝ)
    (hF : ∀ i, Tendsto (F i) (ω : Filter ℕ) (𝓝 (L i))) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧
      ∀ i, Tendsto (fun k ↦ F i (φ k)) atTop (𝓝 (L i)) :=
  exists_strictMono_tendsto_atTop hω F L hF

/-- **The complex-valued corollary**, which is the form the trace comparison
consumes: countably many complex quantities converging along `ω` all converge
along one subsequence in the ordinary sense. -/
theorem exists_strictMono_tendsto_atTop_complex
    {ω : Ultrafilter ℕ} (hω : (ω : Filter ℕ) ≤ cofinite)
    (F : ℕ → ℕ → ℂ) (L : ℕ → ℂ)
    (hF : ∀ i, Tendsto (F i) (ω : Filter ℕ) (𝓝 (L i))) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧
      ∀ i, Tendsto (fun k ↦ F i (φ k)) atTop (𝓝 (L i)) :=
  exists_strictMono_tendsto_atTop hω F L hF

/-- The complex corollary in the `ε`-`N` form, stated with the modulus
`‖F i (φ k) - L i‖` rather than a filter limit: this is the shape an MF-style
definition asks for at each generator. -/
theorem exists_strictMono_norm_sub_lt_complex
    {ω : Ultrafilter ℕ} (hω : (ω : Filter ℕ) ≤ cofinite)
    (F : ℕ → ℕ → ℂ) (L : ℕ → ℂ)
    (hF : ∀ i, Tendsto (F i) (ω : Filter ℕ) (𝓝 (L i))) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧
      ∀ i, ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ k ≥ N, ‖F i (φ k) - L i‖ < ε := by
  obtain ⟨φ, hmono, hφ⟩ := exists_strictMono_tendsto_atTop_complex hω F L hF
  refine ⟨φ, hmono, fun i ε hε ↦ ?_⟩
  obtain ⟨N, hN⟩ := Metric.tendsto_atTop.mp (hφ i) ε hε
  refine ⟨N, fun k hk ↦ ?_⟩
  have h := hN k hk
  rwa [dist_eq_norm] at h

end UltrafilterDiagonalExtraction
end GroupApproximation
