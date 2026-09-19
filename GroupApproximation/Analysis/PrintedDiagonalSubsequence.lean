import GroupApproximation.Analysis.UltrafilterDiagonalExtraction

/-!
# The printed sets `A_j`, and the subsequence chosen from them

Proof-ledger row `NK.07`, the paragraph of `thm:abstract-nk` that turns the
`ω`-statements of the compression paragraph into ordinary ones:

> To obtain ordinary convergence before compressing, pass to a subsequence.
> Enumerate `H̄ = {g₁, g₂, …}`.  For each `j` the set
> `A_j = {n : q_n ≠ 0, max_{i ≤ j} ‖[q_n, V_{g_i,n}]‖ < 1/j,
>          ‖(q_n h_n q_n − θ q_n)_+‖ < 1/j}`
> is again a finite intersection of sets in `ω` … hence lies in `ω` and in
> particular is infinite.  Choose `n₁ < n₂ < ⋯` with `n_j ∈ A_j` and relabel
> along `(n_j)_j`.

`Analysis/UltrafilterDiagonalExtraction` already performs the tolerance half of
this: countably many sequences converging along `ω` all converge along one
subsequence in the ordinary sense.  What it does not carry is the printed first
constraint, `q_n ≠ 0`, which is not a convergence at all but membership of a
prescribed `ω`-large set, and which the print needs because a compression to a
zero corner is no model.

This file adds that constraint.  `exists_strictMono_mem_tendsto_atTop` chooses
the subsequence **inside** a prescribed member of `ω` while still making every
member of a countable family converge in the ordinary sense — the printed `A_j`
with its first clause and its tolerance clauses together.  The argument is the
printed one and adds one line to the argument of the parent file: the set whose
frequency is being asserted is intersected with `A` before the diagonal choice,
and `A ∈ ω` is exactly what keeps that intersection `ω`-large.

Freeness of `ω` is used precisely once, in the same place as in the parent
file: an `ω`-large set is `atTop`-frequent, because a free ultrafilter on `ℕ`
refines `cofinite`, which on `ℕ` is `atTop`.
-/

namespace GroupApproximation
namespace PrintedDiagonalSubsequence

open Filter Topology

/-! ## The extraction, with a prescribed `ω`-large set -/

/-- **Diagonal extraction inside a prescribed `ω`-large set.**  Let `ω` be a
free ultrafilter on `ℕ` and let `A ∈ ω`.  If each member of a countable family
of sequences `F i` converges to `L i` along `ω`, then a single strictly
monotone `φ` takes its values in `A` and makes every `F i ∘ φ` converge to
`L i` along `atTop`.

This is the printed `A_j` construction: the membership constraint is the
printed `q_n ≠ 0`, and the tolerance constraints are the printed `< 1/j`
clauses. -/
theorem exists_strictMono_mem_tendsto_atTop {X : Type*} [PseudoMetricSpace X]
    {ω : Ultrafilter ℕ} (hω : (ω : Filter ℕ) ≤ cofinite)
    {A : Set ℕ} (hA : A ∈ (ω : Filter ℕ))
    (F : ℕ → ℕ → X) (L : ℕ → X)
    (hF : ∀ i, Tendsto (F i) (ω : Filter ℕ) (𝓝 (L i))) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧ (∀ k, φ k ∈ A) ∧
      ∀ i, Tendsto (fun k ↦ F i (φ k)) atTop (𝓝 (L i)) := by
  -- Freeness, in the only form the argument needs.
  have hωtop : (ω : Filter ℕ) ≤ atTop := hω.trans_eq Nat.cofinite_eq_atTop
  -- At tolerance level `k`: the stages that lie in `A` and at which the first
  -- `k + 1` sequences are simultaneously within `1 / (k + 1)` form an
  -- `ω`-large set, hence occur at arbitrarily late stages.  This is the
  -- printed `A_j`.
  have hfreq : ∀ k : ℕ, ∃ᶠ n in atTop,
      n ∈ A ∧
        ∀ i ∈ Finset.range (k + 1), dist (F i n) (L i) < 1 / ((k : ℝ) + 1) := by
    intro k
    have hpos : (0 : ℝ) < 1 / ((k : ℝ) + 1) := by positivity
    have hall : ∀ i ∈ Finset.range (k + 1),
        ∀ᶠ n in (ω : Filter ℕ), dist (F i n) (L i) < 1 / ((k : ℝ) + 1) :=
      fun i _ ↦ Metric.tendsto_nhds.mp (hF i) _ hpos
    have hev : ∀ᶠ n in (ω : Filter ℕ),
        ∀ i ∈ Finset.range (k + 1), dist (F i n) (L i) < 1 / ((k : ℝ) + 1) :=
      (Filter.eventually_all_finset (Finset.range (k + 1))).mpr hall
    have hmem : ∀ᶠ n in (ω : Filter ℕ), n ∈ A := Filter.eventually_mem_set.mpr hA
    exact (hmem.and hev).frequently.filter_mono hωtop
  obtain ⟨φ, hmono, hφ⟩ := extraction_forall_of_frequently hfreq
  refine ⟨φ, hmono, fun k ↦ (hφ k).1, fun i ↦ Metric.tendsto_atTop.mpr fun ε hε ↦ ?_⟩
  obtain ⟨N, hN⟩ := exists_nat_one_div_lt hε
  refine ⟨max i N, fun k hk ↦ ?_⟩
  show dist (F i (φ k)) (L i) < ε
  have hik : i < k + 1 := Nat.lt_succ_of_le ((le_max_left i N).trans hk)
  have hNk : (N : ℝ) + 1 ≤ (k : ℝ) + 1 := by
    have hle : (N : ℝ) ≤ (k : ℝ) := Nat.cast_le.mpr ((le_max_right i N).trans hk)
    linarith
  have hposN : (0 : ℝ) < (N : ℝ) + 1 := by positivity
  have h1 : dist (F i (φ k)) (L i) < 1 / ((k : ℝ) + 1) :=
    (hφ k).2 i (Finset.mem_range.mpr hik)
  have h2 : 1 / ((k : ℝ) + 1) ≤ 1 / ((N : ℝ) + 1) := one_div_le_one_div_of_le hposN hNk
  linarith

/-- The same extraction for a family indexed by an arbitrary countable type,
which is the shape the printed enumeration `H̄ = {g₁, g₂, …}` supplies.
Reindexing along a surjection `ℕ → ι` is all that separates this from
`exists_strictMono_mem_tendsto_atTop`; on an empty index type the tolerance
clauses are vacuous and only the membership constraint survives, which is why
the empty case still runs the extraction rather than returning the identity. -/
theorem exists_strictMono_mem_tendsto_atTop_countable {ι : Type*} [Countable ι]
    {X : Type*} [PseudoMetricSpace X]
    {ω : Ultrafilter ℕ} (hω : (ω : Filter ℕ) ≤ cofinite)
    {A : Set ℕ} (hA : A ∈ (ω : Filter ℕ))
    (F : ι → ℕ → X) (L : ι → X)
    (hF : ∀ i, Tendsto (F i) (ω : Filter ℕ) (𝓝 (L i))) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧ (∀ k, φ k ∈ A) ∧
      ∀ i, Tendsto (fun k ↦ F i (φ k)) atTop (𝓝 (L i)) := by
  rcases isEmpty_or_nonempty ι with hι | _
  · obtain ⟨φ, hmono, hmem, -⟩ :=
      exists_strictMono_mem_tendsto_atTop (X := ℝ) hω hA
        (fun _ _ ↦ (0 : ℝ)) (fun _ ↦ 0) (fun _ ↦ tendsto_const_nhds)
    exact ⟨φ, hmono, hmem, fun i ↦ (hι.false i).elim⟩
  obtain ⟨e, he⟩ := exists_surjective_nat ι
  obtain ⟨φ, hmono, hmem, hφ⟩ :=
    exists_strictMono_mem_tendsto_atTop hω hA (fun j ↦ F (e j)) (fun j ↦ L (e j))
      (fun j ↦ hF (e j))
  refine ⟨φ, hmono, hmem, fun i ↦ ?_⟩
  obtain ⟨j, hj⟩ := he i
  have := hφ j
  rwa [hj] at this

/-- **The printed relabelling, in the form the compression paragraph uses.**
Countably many nonnegative quantities vanishing along `ω`, together with a
prescribed `ω`-large set of stages, are carried onto one subsequence: the
subsequence stays inside the set and every quantity tends to `0` in the
ordinary sense.

The set is the printed `q_n ≠ 0`; the quantities are the printed
`‖[q_n, V_{g,n}]‖` and `‖(q_n h_n q_n − θ q_n)_+‖`. -/
theorem exists_strictMono_mem_tendsto_zero {ι : Type*} [Countable ι]
    {ω : Ultrafilter ℕ} (hω : (ω : Filter ℕ) ≤ cofinite)
    {A : Set ℕ} (hA : A ∈ (ω : Filter ℕ))
    (F : ι → ℕ → ℝ) (hF : ∀ i, Tendsto (F i) (ω : Filter ℕ) (𝓝 0)) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧ (∀ k, φ k ∈ A) ∧
      ∀ i, Tendsto (fun k ↦ F i (φ k)) atTop (𝓝 0) :=
  exists_strictMono_mem_tendsto_atTop_countable hω hA F (fun _ ↦ 0) hF

end PrintedDiagonalSubsequence
end GroupApproximation
