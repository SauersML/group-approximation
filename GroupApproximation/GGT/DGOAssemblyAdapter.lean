import GroupApproximation.GGT.DGOSubdivisionLinear
import GroupApproximation.GGT.DGOSumBoundFinite
import GroupApproximation.GGT.GuessingGeodesicsGrowth

/-!
# The adapter: ℕ-shaped subdivision data meets the calculus lemma

`GGT/DGOSubdivisionLinear.lean` proves that a function obeying a subdivision
recursion is bounded by a linear one.  Its hypothesis is stated in ℝ, indexed by
`Fin k`, and phrased with `Real.log`.  What the geometry produces is none of
those things: side counts are ℕ, the pieces arrive as a range, and the bisection
bounds them with `Nat.log 2`.  This module is the passage, and it is written
**consumer-first** --- the interface here is fixed now, so the assembly can be
written against it rather than the two being reconciled afterwards.

## What the assembly has to hand over

`exists_linear_of_natSubdivision` takes exactly five ℕ facts about the pieces at
each `n > N`:

    k ≤ C' · log₂ n            the piece count
    f n ≤ Σ_{i<k} f (m i)      the recursion
    n ≤ Σ_{i<k} m i            no mass lost
    Σ_{i<k} m i ≤ n + C' · log₂ n   the overhead
    ∀ i < k, 5 · m i ≤ 4 · n   the quarter-separation, at α = 4/5

Nothing else.  If the assembly can produce those, the linear bound follows, and
`sumBound_linear_of_natSubdivision` turns it back into a statement about
`SumBound`.

## The two conversions, and why neither needs a numeric fact

*Indexing.*  `Fin.sum_univ_eq_sum_range` moves between `∑ i : Fin k` and
`∑ i ∈ range k`; the pieces are then a plain `m : ℕ → ℕ` whose values past `k`
are irrelevant, which is easier for the assembly to supply than a `Fin`-indexed
family.

*Logarithms.*  `Nat.log 2 n · log 2 ≤ log n` is immediate from
`2 ^ log₂ n ≤ n` by monotonicity of `Real.log` and `Real.log_pow`, with **no
numeric bound on `log 2`**.  The real constant is then whatever satisfies
`C' ≤ C · log 2`, and `exists_log_constant` produces one from `Real.log_pos`
alone.  Avoiding `log_two_gt_d9` keeps the module free of decimal arithmetic
and of any dependence on how tight that bound is.
-/

namespace GroupApproximation
namespace GGT
namespace DGOPolygonCut

open GroupApproximation.GGT.OsinComponents

universe u w

variable {G : Type u} [Group G] {Λ : Type w}

/-! ## The logarithm bridge -/

/-- **`log₂ n · log 2 ≤ log n`.**  The floor logarithm underestimates the real
one, in the only form the adapter needs and with no decimal arithmetic. -/
theorem natLog_mul_log_two_le (n : ℕ) (hn : 1 ≤ n) :
    (Nat.log 2 n : ℝ) * Real.log 2 ≤ Real.log n := by
  have hpow : (2 : ℕ) ^ Nat.log 2 n ≤ n := Nat.pow_log_le_self 2 (by omega)
  have hcast : ((((2 : ℕ) ^ Nat.log 2 n : ℕ)) : ℝ) ≤ (n : ℝ) := by
    exact_mod_cast hpow
  have hpos : (0 : ℝ) < ((((2 : ℕ) ^ Nat.log 2 n : ℕ)) : ℝ) := by
    exact_mod_cast pow_pos (by norm_num : (0 : ℕ) < 2) (Nat.log 2 n)
  have hmono : Real.log (((2 : ℕ) ^ Nat.log 2 n : ℕ) : ℝ) ≤ Real.log (n : ℝ) :=
    Real.log_le_log hpos hcast
  have hlog : Real.log (((2 : ℕ) ^ Nat.log 2 n : ℕ) : ℝ)
      = (Nat.log 2 n : ℝ) * Real.log 2 := by
    push_cast
    rw [Real.log_pow]
  rw [hlog] at hmono
  exact hmono

/-- **A real constant absorbing the ℕ one.**  `Real.log_pos` is the whole
input. -/
theorem exists_log_constant (C' : ℕ) : ∃ C : ℝ, 0 < C ∧ (C' : ℝ) ≤ C * Real.log 2 := by
  have h2 : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  refine ⟨((C' : ℝ) + 1) / Real.log 2, by positivity, ?_⟩
  rw [div_mul_cancel₀ _ (ne_of_gt h2)]
  linarith

/-! ## The adapter -/

/-- **The calculus lemma, driven by ℕ-shaped subdivision data.**

The interface the assembly targets.  Everything is ℕ and everything is indexed
by a range; the `Fin`-indexing, the casts and the passage from `Nat.log 2` to
`Real.log` all happen here, once. -/
theorem exists_linear_of_natSubdivision (f : ℕ → ℕ) (C' N : ℕ)
    (H : ∀ n : ℕ, N < n → ∃ (k : ℕ) (m : ℕ → ℕ),
      k ≤ C' * Nat.log 2 n ∧
      f n ≤ ∑ i ∈ Finset.range k, f (m i) ∧
      n ≤ ∑ i ∈ Finset.range k, m i ∧
      (∑ i ∈ Finset.range k, m i) ≤ n + C' * Nat.log 2 n ∧
      ∀ i : ℕ, i < k → 5 * m i ≤ 4 * n) :
    ∃ A B : ℝ, 0 ≤ A ∧ 0 ≤ B ∧ ∀ n : ℕ, (f n : ℝ) ≤ A * n + B := by
  obtain ⟨C, hC0, hCle⟩ := exists_log_constant C'
  refine DGO.linear_of_subdivision f C N (4 / 5) hC0 (by norm_num) (by norm_num) ?_
  intro n hn
  obtain ⟨k, m, hk, hf, hlow, hhigh, hquarter⟩ := H n hn
  have hn1 : 1 ≤ n := by omega
  have hnR : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn1
  -- the logarithmic budget, transported once and reused three times
  have hlog : (C' : ℝ) * (Nat.log 2 n : ℝ) ≤ C * Real.log n := by
    have hbridge := natLog_mul_log_two_le n hn1
    have hnn : (0 : ℝ) ≤ (Nat.log 2 n : ℝ) := Nat.cast_nonneg _
    nlinarith [hnn, hbridge, hCle, hC0.le]
  refine ⟨k, fun i => m i, ?_, ?_, ?_, ?_, ?_⟩
  · have : (k : ℝ) ≤ (C' : ℝ) * (Nat.log 2 n : ℝ) := by exact_mod_cast hk
    linarith
  · rw [Fin.sum_univ_eq_sum_range (fun i => (f (m i) : ℝ)) k]
    have : ((∑ i ∈ Finset.range k, f (m i) : ℕ) : ℝ)
        = ∑ i ∈ Finset.range k, (f (m i) : ℝ) := by push_cast; rfl
    rw [← this]
    exact_mod_cast hf
  · rw [Fin.sum_univ_eq_sum_range (fun i => (m i : ℝ)) k]
    have : ((∑ i ∈ Finset.range k, m i : ℕ) : ℝ)
        = ∑ i ∈ Finset.range k, (m i : ℝ) := by push_cast; rfl
    rw [← this]
    exact_mod_cast hlow
  · rw [Fin.sum_univ_eq_sum_range (fun i => (m i : ℝ)) k]
    have hcast : ((∑ i ∈ Finset.range k, m i : ℕ) : ℝ)
        = ∑ i ∈ Finset.range k, (m i : ℝ) := by push_cast; rfl
    rw [← hcast]
    have : ((∑ i ∈ Finset.range k, m i : ℕ) : ℝ)
        ≤ (n : ℝ) + (C' : ℝ) * (Nat.log 2 n : ℝ) := by exact_mod_cast hhigh
    linarith
  · intro i
    have hi : (i : ℕ) < k := i.isLt
    have h5 : (5 : ℝ) * (m i : ℝ) ≤ 4 * (n : ℝ) := by
      exact_mod_cast hquarter i hi
    linarith

/-! ## The quarter-separation threshold -/

/-- **Past a threshold, a quarter-separated cut leaves both halves below `4n/5`.**

The `α = 4/5` clause of the subdivision recursion, in the form the two halves
supply it.  A cut at sides `a < b` with `n ≤ 4(b−a) ≤ 3n` gives halves of
`b−a+1+L` and `n−b+a+1+L` sides, `L` being the chord's contribution, and both
are below `4n/5` as soon as `20 + 20L ≤ n`.

Both bounds reduce to that single condition, from opposite ends of the window:
the first uses `4(b−a) ≤ 3n` directly, and the second uses `n ≤ 4(b−a)` through
`4((n−b)+a) = 4n − 4(b−a) ≤ 3n`.  So the quarter-separation is doing exactly the
work its name suggests --- neither half can be the big one.

The threshold itself is `exists_radius_log_lt`, the growth comparison built for
Bowditch's criterion: `L` is logarithmic in `n`, so `20 + 20L ≤ n` eventually.
Nothing here depends on how the cut was produced, only on the window it
satisfies. -/
theorem exists_quarter_threshold (C' : ℕ) :
    ∃ N : ℕ, ∀ n L a b : ℕ, N < n → L ≤ C' * Nat.log 2 n →
      b < n → n ≤ 4 * (b - a) → 4 * (b - a) ≤ 3 * n →
      5 * ((b - a + 1) + L) ≤ 4 * n ∧ 5 * ((n - b) + a + 1 + L) ≤ 4 * n := by
  obtain ⟨r, hr⟩ := OsinEnlargement.exists_radius_log_lt (20 * C') 20
  refine ⟨r, ?_⟩
  intro n L a b hn hL hbn hlow hupp
  have hgrow := hr n hn
  have hLn : 20 * L ≤ 20 * (C' * Nat.log 2 n) := by
    exact Nat.mul_le_mul (le_refl 20) hL
  have hexp : 20 * C' * (Nat.log 2 n + 1) + 20
      = 20 * (C' * Nat.log 2 n) + (20 * C' + 20) := by ring
  rw [hexp] at hgrow
  -- `n - b + a = n - (b - a)`, which is where the second bound gets its slack
  have hsplit : (n - b) + a = n - (b - a) := by omega
  rw [hsplit]
  omega

/-! ## Proposition 4.14, once the assembly exists -/

/-- **The uniform linear sum bound**, modulo the assignment.

This is Dahmani--Guirardel--Osin's Proposition 4.14 in the settled `∃ r` form:
a constant linear in the side count, uniform over all polygons.  Its one
geometric hypothesis is the subdivision recursion for the least admissible
constant --- precisely what the assembly is being built to produce --- so when
that lands, 4.14 closes by composition and nothing further is required here.

The conclusion is `A * n + B` rather than `D * n` because the two differ only at
`n = 0`, where no polygon exists; a consumer at `n ≥ 1` takes `D := A + B`. -/
theorem sumBound_linear_of_natSubdivision (D : RelGenSet G Λ) (b : ℝ)
    (hfin : ∀ n : ℕ, ∃ K : ℕ, SumBound D b n K) (C' N : ℕ)
    (H : ∀ n : ℕ, N < n → ∃ (k : ℕ) (m : ℕ → ℕ),
      k ≤ C' * Nat.log 2 n ∧
      sumConst (hfin n) ≤ ∑ i ∈ Finset.range k, sumConst (hfin (m i)) ∧
      n ≤ ∑ i ∈ Finset.range k, m i ∧
      (∑ i ∈ Finset.range k, m i) ≤ n + C' * Nat.log 2 n ∧
      ∀ i : ℕ, i < k → 5 * m i ≤ 4 * n) :
    ∃ A B : ℕ, ∀ n : ℕ, SumBound D b n (A * n + B) := by
  obtain ⟨A, B, hA0, hB0, hlin⟩ :=
    exists_linear_of_natSubdivision (fun n => sumConst (hfin n)) C' N H
  refine ⟨⌈A⌉₊, ⌈B⌉₊, ?_⟩
  intro n
  refine SumBound.mono (sumBound_sumConst (hfin n)) ?_
  have hbound : (sumConst (hfin n) : ℝ) ≤ A * n + B := hlin n
  have hAle : A ≤ (⌈A⌉₊ : ℝ) := Nat.le_ceil A
  have hBle : B ≤ (⌈B⌉₊ : ℝ) := Nat.le_ceil B
  have hn0 : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
  have hfinal : (sumConst (hfin n) : ℝ) ≤ (⌈A⌉₊ : ℝ) * n + (⌈B⌉₊ : ℝ) := by
    nlinarith [hbound, hAle, hBle, hn0]
  exact_mod_cast hfinal

end DGOPolygonCut
end GGT
end GroupApproximation
