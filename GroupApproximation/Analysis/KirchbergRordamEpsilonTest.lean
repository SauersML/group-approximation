import Mathlib.Order.Filter.AtTopBot.Basic
import Mathlib.Topology.MetricSpace.Basic
import Mathlib.Analysis.SpecificLimits.Basic

/-!
# Kirchberg's `ε`-test

Kirchberg--Rørdam, *Central sequence C⋆-algebras and tensorial absorption of
the Jiang--Su algebra*, J. reine angew. Math. **695** (2014), 215--282,
Lemma 3.1.  This is the combinatorial engine of their corona theory, and it is
completely elementary: a diagonal argument over a sequence of index sets.  It
is **proved here**, not assumed.

## The statement

Let `X 0, X 1, X 2, …` be sets and let `x` range over the product `∀ n, X n`.
Suppose that for each `k` we are given a sequence of nonnegative "defect"
functions `f k n : X n → ℝ`, and that

> for every finite list of defects `k ≤ m` and every tolerance `ε > 0` there is
> a point of the product along which all of `f 0, …, f m` are eventually
> below `ε`.

Then **one single point of the product** kills *all* the defects at once:
`f k n (x n) → 0` for every `k`.

The hypothesis is one tolerance at a time and finitely many defects at a time;
the conclusion is all defects simultaneously and exactly zero.  That is the
whole force of the lemma, and it is why the corona algebra `∏ Mₖ / ⊕ Mₖ`
behaves like a countably saturated object: a countable family of approximate
requirements, each individually satisfiable, is satisfiable *exactly* in the
corona.

## Why the sequence structure is essential

Without the `∀ᶠ n` --- i.e. for a family of functions on a *fixed* set --- the
statement is false: take `X = ℕ` and `f k (x) = 1/x`, where every finite
subfamily can be made small but no point makes them zero.  The `atTop` filter
is what lets the diagonal be assembled in blocks, each block borrowing the
witness of a later and better approximation.

## The proof, in one paragraph

Apply the hypothesis with `m` defects and tolerance `1/(m+1)` to get a witness
`x⁽ᵐ⁾` and a stage `N m` beyond which all of `f 0, …, f m` are below
`1/(m+1)` along `x⁽ᵐ⁾`.  Inflate `N` to a strictly increasing `stepBound`, and
define the diagonal by reading, at coordinate `n`, the witness `x⁽ʲ⁾` for the
block `j` that `n` falls in.  Beyond `stepBound m₀` the block index is at
least `m₀`, so every fixed defect `k ≤ m₀` is below `1/(m₀+1)` from there on.
-/

namespace GroupApproximation
namespace KirchbergRordam

open Filter

universe u

/-! ## Block bounds -/

/-- The strictly increasing inflation of a sequence of stages: `stepBound N m`
is at least `N m`, and strictly increasing in `m`.  Ordinary `N` need not be
monotone, and the diagonal argument needs blocks that genuinely advance. -/
def stepBound (N : ℕ → ℕ) : ℕ → ℕ
  | 0 => N 0
  | (m + 1) => max (stepBound N m + 1) (N (m + 1))

theorem stepBound_lt_succ (N : ℕ → ℕ) (m : ℕ) :
    stepBound N m < stepBound N (m + 1) :=
  lt_of_lt_of_le (Nat.lt_succ_self _) (le_max_left _ _)

theorem strictMono_stepBound (N : ℕ → ℕ) : StrictMono (stepBound N) :=
  strictMono_nat_of_lt_succ (stepBound_lt_succ N)

theorem le_stepBound (N : ℕ → ℕ) : ∀ m : ℕ, N m ≤ stepBound N m
  | 0 => le_rfl
  | (_m + 1) => le_max_right _ _

theorem self_le_stepBound (N : ℕ → ℕ) : ∀ m : ℕ, m ≤ stepBound N m
  | 0 => Nat.zero_le _
  | (m + 1) => by
      have h1 : m ≤ stepBound N m := self_le_stepBound N m
      have h2 : stepBound N m + 1 ≤ stepBound N (m + 1) := le_max_left _ _
      omega

/-! ## Collecting finitely many eventual conditions -/

/-- Finitely many `∀ᶠ` statements may be collected into one.  Stated for the
initial segment `k ≤ m` because that is the indexing the `ε`-test uses. -/
theorem eventually_forall_le {l : Filter ℕ} {p : ℕ → ℕ → Prop} :
    ∀ (m : ℕ), (∀ k ≤ m, ∀ᶠ n in l, p k n) → ∀ᶠ n in l, ∀ k ≤ m, p k n := by
  intro m
  induction m with
  | zero =>
      intro h
      filter_upwards [h 0 le_rfl] with n hn k hk
      rw [Nat.le_zero.mp hk]
      exact hn
  | succ m ih =>
      intro h
      have h' : ∀ k ≤ m, ∀ᶠ n in l, p k n := fun k hk =>
        h k (hk.trans (Nat.le_succ m))
      filter_upwards [ih h', h (m + 1) le_rfl] with n hn hn1 k hk
      rcases eq_or_lt_of_le hk with rfl | hlt
      · exact hn1
      · exact hn k (Nat.lt_succ_iff.mp hlt)

/-! ## The `ε`-test -/

/-- **Kirchberg's `ε`-test** (Kirchberg--Rørdam 2014, Lemma 3.1).

If every finite family of nonnegative defects can be made eventually smaller
than every prescribed tolerance by *some* point of the product `∀ n, X n`,
then a single point of the product makes *every* defect tend to zero. -/
theorem epsilon_test {X : ℕ → Type u} (f : ℕ → ∀ n : ℕ, X n → ℝ)
    (hf : ∀ (k n : ℕ) (y : X n), 0 ≤ f k n y)
    (h : ∀ (m : ℕ) (ε : ℝ), 0 < ε →
      ∃ x : ∀ n, X n, ∀ k ≤ m, ∀ᶠ n in atTop, f k n (x n) < ε) :
    ∃ x : ∀ n, X n, ∀ k : ℕ, Tendsto (fun n => f k n (x n)) atTop (nhds 0) := by
  classical
  -- Stage 1: one witness and one stage per tolerance `1/(m+1)`.
  have key : ∀ m : ℕ, ∃ (y : ∀ n, X n) (N : ℕ),
      ∀ n ≥ N, ∀ k ≤ m, f k n (y n) < 1 / (m + 1) := by
    intro m
    obtain ⟨y, hy⟩ := h m (1 / (m + 1)) (by positivity)
    obtain ⟨N, hN⟩ := eventually_atTop.mp (eventually_forall_le m hy)
    exact ⟨y, N, hN⟩
  choose y N hyN using key
  -- Stage 2: the blocks.
  have hex : ∀ n : ℕ, ∃ m : ℕ, n < stepBound N (m + 1) := fun n =>
    ⟨n, lt_of_lt_of_le (Nat.lt_succ_self n) (self_le_stepBound N (n + 1))⟩
  refine ⟨fun n => y (Nat.find (hex n)) n, ?_⟩
  intro k
  rw [Metric.tendsto_atTop]
  intro ε hε
  -- Stage 3: choose a block index past `k` whose tolerance beats `ε`.
  obtain ⟨m₁, hm₁⟩ := exists_nat_one_div_lt hε
  refine ⟨stepBound N (max k m₁), ?_⟩
  intro n hn
  show dist (f k n (y (Nat.find (hex n)) n)) 0 < ε
  set j := Nat.find (hex n) with hjdef
  -- the block index at `n` is at least `max k m₁`
  have hjge : max k m₁ ≤ j := by
    by_contra hcon
    have hlt : j < max k m₁ := Nat.not_le.mp hcon
    have h1 : n < stepBound N (j + 1) := Nat.find_spec (hex n)
    have h2 : stepBound N (j + 1) ≤ stepBound N (max k m₁) :=
      (strictMono_stepBound N).monotone hlt
    omega
  -- and the stage `N j` has been passed
  have hjN : N j ≤ n := by
    rcases Nat.eq_zero_or_pos j with hj0 | hjpos
    · have h0 : N 0 ≤ stepBound N 0 := le_stepBound N 0
      have h1 : stepBound N 0 ≤ stepBound N (max k m₁) :=
        (strictMono_stepBound N).monotone (Nat.zero_le _)
      rw [hj0]
      omega
    · have h1 : ¬ (n < stepBound N ((j - 1) + 1)) :=
        Nat.find_min (hex n) (by omega)
      have h2 : (j - 1) + 1 = j := Nat.succ_pred_eq_of_pos hjpos
      rw [h2] at h1
      have h3 : N j ≤ stepBound N j := le_stepBound N j
      omega
  -- the defect at `n` is below the block's tolerance, which is below `ε`
  have hkj : k ≤ j := le_trans (le_max_left k m₁) hjge
  have hval : f k n (y j n) < 1 / (j + 1) := hyN j n hjN k hkj
  have hstep : (1 : ℝ) / (j + 1) ≤ 1 / (m₁ + 1) := by
    refine one_div_le_one_div_of_le (by positivity) ?_
    have : (m₁ : ℝ) ≤ (j : ℝ) := by
      exact_mod_cast le_trans (le_max_right k m₁) hjge
    linarith
  have hnonneg : 0 ≤ f k n (y j n) := hf k n (y j n)
  rw [Real.dist_eq, sub_zero, abs_of_nonneg hnonneg]
  calc f k n (y j n) < 1 / (j + 1) := hval
    _ ≤ 1 / (m₁ + 1) := hstep
    _ < ε := hm₁

/-! ## The form applications use -/

/-- **The `ε`-test at a countable family of conditions.**  A restatement of
`epsilon_test` in the shape in which the corona applications meet it: a
countable family of "requirements" `f k`, each of which can be met to
arbitrary precision by some sequence, is met exactly by one sequence.

The only difference from `epsilon_test` is that the hypothesis is phrased with
a `Finset` of indices rather than an initial segment, which is how a
requirement list is normally produced. -/
theorem epsilon_test_finset {X : ℕ → Type u} (f : ℕ → ∀ n : ℕ, X n → ℝ)
    (hf : ∀ (k n : ℕ) (z : X n), 0 ≤ f k n z)
    (h : ∀ (s : Finset ℕ) (ε : ℝ), 0 < ε →
      ∃ x : ∀ n, X n, ∀ k ∈ s, ∀ᶠ n in atTop, f k n (x n) < ε) :
    ∃ x : ∀ n, X n, ∀ k : ℕ, Tendsto (fun n => f k n (x n)) atTop (nhds 0) := by
  refine epsilon_test f hf ?_
  intro m ε hε
  obtain ⟨x, hx⟩ := h (Finset.range (m + 1)) ε hε
  exact ⟨x, fun k hk => hx k (Finset.mem_range.mpr (Nat.lt_succ_of_le hk))⟩

end KirchbergRordam
end GroupApproximation
