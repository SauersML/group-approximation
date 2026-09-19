import Mathlib.Analysis.Real.Sqrt
import Mathlib.Analysis.SpecialFunctions.Log.Basic

/-!
# Subdivision with logarithmic overhead forces linearity

Module 3 of the DGO Proposition 4.14 campaign: the arithmetic lemma DGO
state as Lemma 4.19 (`linfunct` in `HE.tex:504`) **without proof**.  If
`f : ℕ → ℕ` carries, for every large `n`, a subdivision into at most
`C ln n` pieces of size at most `αn`, of total size between `n` and
`n + C ln n`, with `f(n)` bounded by the sum of `f` over the pieces, then
`f` is linearly bounded.

**The proof** (reconstructed; no source carries one): strong induction with
the potential `A·(n − √n) + B`.  The one inequality that beats the
logarithmic overhead is elementary: each piece satisfies `mᵢ ≤ αn`, so
`√mᵢ ≥ mᵢ/√(αn)`, and summing against the lower bound `Σmᵢ ≥ n` gives
`Σ√mᵢ ≥ √n/√α = (1 + ε)·√n`-worth of square-root mass, a *gain* of
`ε√n` over the potential's debit — while the overhead costs only
`O(C log n)`, which `ε√n` eventually dominates.  The threshold where it
does depends only on `C` and `α`, so no circularity enters the choice of
`A` and `B`.  Two purely algebraic devices keep the file division-free:
`1/√α ≥ 1 + (1 − √α)` is `(1 − √α)² ≥ 0` in disguise, and
`log n ≤ 4·√√n` comes from `log x ≤ x − 1` applied at `√√n`.

The consumer is the 4.14 assembly: `f := s_{μ,c}` with the subdivision
supplied by the balanced bisection (`OlshanskiiBisection`) and the base
cases by the small-polygon estimates.  This module is deliberately
self-contained arithmetic — it imports only Mathlib.
-/

namespace GroupApproximation
namespace DGO

open Finset

/-- **Subdivision with any square-root-negligible overhead forces linearity.**

`pieceOverhead` bounds the number of children and `sizeOverhead` bounds the
excess of their total size over the parent.  The proof only needs their sum to
be eventually dominated by the square-root gain in the potential
`A * (n - √n) + B`.  This is the robust form of DGO Lemma 4.19; both the
printed logarithmic overhead and the corrected squared-logarithmic overhead
from unordered chord partners are instances. -/
theorem linear_of_subdivision_of_sqrt_overhead (f : ℕ → ℕ)
    (pieceOverhead sizeOverhead : ℕ → ℝ) (N : ℕ) (α ε : ℝ) (M₁ : ℕ)
    (hα0 : 0 < α) (hα1 : α < 1) (hε0 : 0 < ε)
    (hgain : Real.sqrt α * (1 + ε) ≤ 1)
    (hthresh : ∀ n : ℕ, M₁ < n →
      sizeOverhead n + pieceOverhead n ≤ ε * Real.sqrt n)
    (H : ∀ n : ℕ, N < n → ∃ (k : ℕ) (m : Fin k → ℕ),
      (k : ℝ) ≤ pieceOverhead n ∧
      (f n : ℝ) ≤ ∑ i, (f (m i) : ℝ) ∧
      (n : ℝ) ≤ ∑ i, (m i : ℝ) ∧
      (∑ i, (m i : ℝ)) ≤ (n : ℝ) + sizeOverhead n ∧
      ∀ i, (m i : ℝ) ≤ α * n) :
    ∃ A B : ℝ, 0 ≤ A ∧ 0 ≤ B ∧
      ∀ n : ℕ, (f n : ℝ) ≤ A * n + B := by
  set sα : ℝ := Real.sqrt α with hsαdef
  have hgain' : sα * (1 + ε) ≤ 1 := by simpa [hsαdef] using hgain
  set M₀ : ℕ := max (max N M₁) 1 with hM₀def
  set B : ℝ := (((Finset.range (M₀ + 1)).sup f : ℕ) : ℝ) with hBdef
  have hB0 : 0 ≤ B := by
    rw [hBdef]
    exact Nat.cast_nonneg _
  have hBbase : ∀ n : ℕ, n ≤ M₀ → (f n : ℝ) ≤ B := by
    intro n hn
    rw [hBdef]
    have hmem : n ∈ Finset.range (M₀ + 1) := Finset.mem_range.mpr (by omega)
    have hle : f n ≤ (Finset.range (M₀ + 1)).sup f := Finset.le_sup hmem
    exact_mod_cast hle
  set A : ℝ := max B 1 with hAdef
  have hA0 : 0 < A := lt_of_lt_of_le one_pos (le_max_right B 1)
  have hBA : B ≤ A := le_max_left B 1
  -- the potential is nonnegative
  have hpot : ∀ n : ℕ, 0 ≤ (n : ℝ) - Real.sqrt n := by
    intro n
    rcases Nat.eq_zero_or_pos n with h0 | hpos
    · rw [h0]
      norm_num
    · have h1 : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hpos
      have hsq : Real.sqrt n ≤ n := by
        rw [Real.sqrt_le_left (by linarith)]
        nlinarith
      linarith
  -- the strong induction with potential `A(n − √n) + B`
  have hmain : ∀ n : ℕ, (f n : ℝ) ≤ A * ((n : ℝ) - Real.sqrt n) + B := by
    intro n
    induction n using Nat.strong_induction_on with
    | _ n ih =>
      rcases le_or_gt n M₀ with hbase | hstep
      · -- base: the potential is nonnegative and `B` dominates
        have h1 := hBbase n hbase
        have h2 : 0 ≤ A * ((n : ℝ) - Real.sqrt n) :=
          mul_nonneg (le_of_lt hA0) (hpot n)
        linarith
      · -- step
        have hnN : N < n :=
          lt_of_le_of_lt (le_trans (le_max_left N M₁) (le_max_left _ 1)) hstep
        obtain ⟨k, m, hk, hf, hlow, hup, hsmall⟩ := H n hnN
        have hn1 : (1 : ℝ) ≤ (n : ℝ) := by
          have : 1 ≤ n := le_trans (le_max_right (max N M₁) 1) (le_of_lt hstep)
          exact_mod_cast this
        have hn0 : (0 : ℝ) < (n : ℝ) := lt_of_lt_of_le one_pos hn1
        -- each piece is strictly smaller
        have hlt : ∀ i, m i < n := by
          intro i
          have h1 : (m i : ℝ) ≤ α * n := hsmall i
          have h2 : α * n < 1 * n := by
            exact mul_lt_mul_of_pos_right hα1 hn0
          rw [one_mul] at h2
          exact_mod_cast lt_of_le_of_lt h1 h2
        -- apply the induction hypothesis across the pieces
        have hsum : (f n : ℝ) ≤
            A * (∑ i, (m i : ℝ)) - A * (∑ i, Real.sqrt (m i)) + k * B := by
          have hstep1 : ∀ i : Fin k, (f (m i) : ℝ) ≤
              A * ((m i : ℝ) - Real.sqrt (m i)) + B := fun i => ih (m i) (hlt i)
          have hsum1 : (∑ i, (f (m i) : ℝ)) ≤
              ∑ i, (A * ((m i : ℝ) - Real.sqrt (m i)) + B) :=
            Finset.sum_le_sum fun i _ => hstep1 i
          have hexpand : (∑ i, (A * ((m i : ℝ) - Real.sqrt (m i)) + B)) =
              A * (∑ i, (m i : ℝ)) - A * (∑ i, Real.sqrt (m i)) + k * B := by
            rw [Finset.sum_add_distrib, ← Finset.mul_sum,
              Finset.sum_sub_distrib, mul_sub, Finset.sum_const,
              Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
          calc (f n : ℝ) ≤ ∑ i, (f (m i) : ℝ) := hf
            _ ≤ ∑ i, (A * ((m i : ℝ) - Real.sqrt (m i)) + B) := hsum1
            _ = A * (∑ i, (m i : ℝ)) - A * (∑ i, Real.sqrt (m i)) + k * B := hexpand
        -- the square-root mass gain: `Σ√mᵢ ≥ (1+ε)√n`
        have hmass : (1 + ε) * Real.sqrt n ≤ ∑ i, Real.sqrt (m i) := by
          have hS0 : 0 ≤ ∑ i, Real.sqrt (m i) :=
            Finset.sum_nonneg fun i _ => Real.sqrt_nonneg _
          -- each `mᵢ ≤ √mᵢ · (sα √n)`
          have hper : ∀ i : Fin k, (m i : ℝ) ≤
              Real.sqrt (m i) * (sα * Real.sqrt n) := by
            intro i
            have h2 : Real.sqrt (m i) ≤ Real.sqrt (α * n) :=
              Real.sqrt_le_sqrt (hsmall i)
            have h3 : Real.sqrt (α * n) = sα * Real.sqrt n := by
              rw [hsαdef]
              exact Real.sqrt_mul (le_of_lt hα0) _
            have h4 : Real.sqrt (m i) ≤ sα * Real.sqrt n := by
              rw [← h3]
              exact h2
            calc (m i : ℝ) = Real.sqrt (m i) * Real.sqrt (m i) :=
                  (Real.mul_self_sqrt (Nat.cast_nonneg _)).symm
              _ ≤ Real.sqrt (m i) * (sα * Real.sqrt n) :=
                  mul_le_mul_of_nonneg_left h4 (Real.sqrt_nonneg _)
          -- sum: `n ≤ (Σ√mᵢ) · (sα √n)`
          have hsum2 : (n : ℝ) ≤ (∑ i, Real.sqrt (m i)) * (sα * Real.sqrt n) := by
            calc (n : ℝ) ≤ ∑ i, (m i : ℝ) := hlow
              _ ≤ ∑ i, Real.sqrt (m i) * (sα * Real.sqrt n) :=
                  Finset.sum_le_sum fun i _ => hper i
              _ = (∑ i, Real.sqrt (m i)) * (sα * Real.sqrt n) :=
                  (Finset.sum_mul _ _ _).symm
        -- cancel one `√n` and spend the gain inequality
          have hnn : (n : ℝ) = Real.sqrt n * Real.sqrt n :=
            (Real.mul_self_sqrt (le_of_lt hn0)).symm
          have hsn0 : 0 < Real.sqrt n := Real.sqrt_pos.mpr hn0
          have hcancel : Real.sqrt n ≤ (∑ i, Real.sqrt (m i)) * sα := by
            have h1 : Real.sqrt n * Real.sqrt n ≤
                ((∑ i, Real.sqrt (m i)) * sα) * Real.sqrt n := by
              rw [← hnn]
              calc (n : ℝ) ≤ (∑ i, Real.sqrt (m i)) * (sα * Real.sqrt n) := hsum2
                _ = ((∑ i, Real.sqrt (m i)) * sα) * Real.sqrt n := by ring
            exact le_of_mul_le_mul_right (by linarith [h1]) hsn0
          calc (1 + ε) * Real.sqrt n
              ≤ (1 + ε) * ((∑ i, Real.sqrt (m i)) * sα) := by
                have h10 : (0 : ℝ) ≤ 1 + ε := by linarith
                exact mul_le_mul_of_nonneg_left hcancel h10
            _ = (∑ i, Real.sqrt (m i)) * (sα * (1 + ε)) := by ring
            _ ≤ (∑ i, Real.sqrt (m i)) * 1 :=
                mul_le_mul_of_nonneg_left hgain' hS0
            _ = ∑ i, Real.sqrt (m i) := mul_one _
        -- overhead bookkeeping and the close
        have hkB : (k : ℝ) * B ≤ pieceOverhead n * A := by
          have h1 : (k : ℝ) * B ≤ pieceOverhead n * B := by
            have := mul_le_mul_of_nonneg_right hk hB0
            linarith
          have h2 : pieceOverhead n * B ≤ pieceOverhead n * A := by
            have hpiece : 0 ≤ pieceOverhead n :=
              (Nat.cast_nonneg k).trans hk
            exact mul_le_mul_of_nonneg_left hBA hpiece
          linarith
        have hM₁n : M₁ < n :=
          lt_of_le_of_lt (le_trans (le_max_right N M₁) (le_max_left _ 1)) hstep
        have hth := hthresh n hM₁n
        have hfinal : (f n : ℝ) ≤ A * ((n : ℝ) - Real.sqrt n) + B := by
          have h1 : A * (∑ i, (m i : ℝ)) ≤
              A * ((n : ℝ) + sizeOverhead n) :=
            mul_le_mul_of_nonneg_left hup (le_of_lt hA0)
          have h2 : A * ((1 + ε) * Real.sqrt n) ≤ A * (∑ i, Real.sqrt (m i)) :=
            mul_le_mul_of_nonneg_left hmass (le_of_lt hA0)
          have h3 : A * (sizeOverhead n + pieceOverhead n) ≤
              A * (ε * Real.sqrt n) :=
            mul_le_mul_of_nonneg_left hth (le_of_lt hA0)
          nlinarith [hsum, hkB]
        exact hfinal
  refine ⟨A, B, le_of_lt hA0, hB0, ?_⟩
  intro n
  have h1 := hmain n
  have h2 : A * ((n : ℝ) - Real.sqrt n) ≤ A * n := by
    have hs : 0 ≤ Real.sqrt n := Real.sqrt_nonneg _
    have := mul_le_mul_of_nonneg_left (by linarith : (n : ℝ) - Real.sqrt n ≤ n)
      (le_of_lt hA0)
    exact this
  linarith

/-- **Subdivision with logarithmic overhead forces linearity** (DGO
Lemma 4.19, stated there without proof).  This is the printed instance of
`linear_of_subdivision_of_sqrt_overhead`. -/
theorem linear_of_subdivision (f : ℕ → ℕ) (C : ℝ) (N : ℕ) (α : ℝ)
    (hC : 0 < C) (hα0 : 0 < α) (hα1 : α < 1)
    (H : ∀ n : ℕ, N < n → ∃ (k : ℕ) (m : Fin k → ℕ),
      (k : ℝ) ≤ C * Real.log n ∧
      (f n : ℝ) ≤ ∑ i, (f (m i) : ℝ) ∧
      (n : ℝ) ≤ ∑ i, (m i : ℝ) ∧
      (∑ i, (m i : ℝ)) ≤ (n : ℝ) + C * Real.log n ∧
      ∀ i, (m i : ℝ) ≤ α * n) :
    ∃ A B : ℝ, 0 ≤ A ∧ 0 ≤ B ∧
      ∀ n : ℕ, (f n : ℝ) ≤ A * n + B := by
  let sα : ℝ := Real.sqrt α
  let ε : ℝ := 1 - sα
  have hsα0 : 0 < sα := Real.sqrt_pos.mpr hα0
  have hsα1 : sα < 1 := by
    dsimp [sα]
    nlinarith [Real.mul_self_sqrt (le_of_lt hα0)]
  have hε0 : 0 < ε := by dsimp [ε]; linarith
  have hgain : Real.sqrt α * (1 + ε) ≤ 1 := by
    have hsq : 0 ≤ (1 - sα) * (1 - sα) :=
      mul_nonneg (by linarith) (by linarith)
    dsimp [ε, sα] at hsq ⊢
    nlinarith
  let x₀ : ℝ := 8 * C / ε
  have hx₀0 : 0 < x₀ := by dsimp [x₀]; positivity
  let M₁ : ℕ := Nat.ceil (x₀ ^ 4)
  have hthresh : ∀ n : ℕ, M₁ < n →
      (C * Real.log n) + (C * Real.log n) ≤ ε * Real.sqrt n := by
    intro n hn
    have hnM₁ : M₁ ≤ n := le_of_lt hn
    have hn1Nat : 1 ≤ n := by omega
    have hn1 : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn1Nat
    have hn0 : (0 : ℝ) < (n : ℝ) := lt_of_lt_of_le one_pos hn1
    let r : ℝ := Real.sqrt (Real.sqrt n)
    have hr0 : 0 < r := Real.sqrt_pos.mpr (Real.sqrt_pos.mpr hn0)
    have hrr : r * r = Real.sqrt n := by
      dsimp [r]
      exact Real.mul_self_sqrt (Real.sqrt_nonneg _)
    have hlog4 : Real.log n = 4 * Real.log r := by
      dsimp [r]
      rw [Real.log_sqrt (Real.sqrt_nonneg _), Real.log_sqrt (le_of_lt hn0)]
      ring
    have hlogr : Real.log r ≤ r := by
      have h := Real.log_le_sub_one_of_pos hr0
      linarith
    have hn4 : x₀ ^ 4 ≤ (n : ℝ) := by
      have hceil : x₀ ^ 4 ≤ (M₁ : ℝ) := by
        dsimp [M₁]
        exact Nat.le_ceil _
      have hcast : (M₁ : ℝ) ≤ (n : ℝ) := by exact_mod_cast hnM₁
      linarith
    have hrx₀ : x₀ ≤ r := by
      have h1 : Real.sqrt (x₀ ^ 4) ≤ Real.sqrt n := Real.sqrt_le_sqrt hn4
      have h2 : Real.sqrt (x₀ ^ 4) = x₀ ^ 2 := by
        have hpow : x₀ ^ 4 = (x₀ ^ 2) ^ 2 := by ring
        rw [hpow]
        exact Real.sqrt_sq (by positivity)
      have h3 : Real.sqrt (x₀ ^ 2) ≤ r := by
        dsimp [r]
        apply Real.sqrt_le_sqrt
        rw [← h2]
        exact h1
      rw [Real.sqrt_sq (le_of_lt hx₀0)] at h3
      exact h3
    have hx₀ε : ε * x₀ = 8 * C := by
      dsimp [x₀]
      field_simp
    have hmain : 2 * C * Real.log n ≤ ε * Real.sqrt n := by
      calc
        2 * C * Real.log n = 8 * C * Real.log r := by rw [hlog4]; ring
        _ ≤ 8 * C * r := by
          exact mul_le_mul_of_nonneg_left hlogr (by positivity)
        _ = ε * x₀ * r := by rw [hx₀ε]
        _ ≤ ε * r * r := by
          have h := mul_le_mul_of_nonneg_left hrx₀ (le_of_lt hε0)
          nlinarith
        _ = ε * Real.sqrt n := by rw [mul_assoc, hrr]
    linarith
  exact linear_of_subdivision_of_sqrt_overhead f
    (fun n => C * Real.log n) (fun n => C * Real.log n) N α ε M₁
    hα0 hα1 hε0 hgain hthresh H

/-- Natural-number conclusion for the robust square-root-overhead lemma. -/
theorem nat_linear_of_subdivision_of_sqrt_overhead (f : ℕ → ℕ)
    (pieceOverhead sizeOverhead : ℕ → ℝ) (N : ℕ) (α ε : ℝ) (M₁ : ℕ)
    (hα0 : 0 < α) (hα1 : α < 1) (hε0 : 0 < ε)
    (hgain : Real.sqrt α * (1 + ε) ≤ 1)
    (hthresh : ∀ n : ℕ, M₁ < n →
      sizeOverhead n + pieceOverhead n ≤ ε * Real.sqrt n)
    (H : ∀ n : ℕ, N < n → ∃ (k : ℕ) (m : Fin k → ℕ),
      (k : ℝ) ≤ pieceOverhead n ∧
      (f n : ℝ) ≤ ∑ i, (f (m i) : ℝ) ∧
      (n : ℝ) ≤ ∑ i, (m i : ℝ) ∧
      (∑ i, (m i : ℝ)) ≤ (n : ℝ) + sizeOverhead n ∧
      ∀ i, (m i : ℝ) ≤ α * n) :
    ∃ L : ℕ, ∀ n : ℕ, 1 ≤ n → f n ≤ L * n := by
  obtain ⟨A, B, hA, hB, hlin⟩ :=
    linear_of_subdivision_of_sqrt_overhead f pieceOverhead sizeOverhead
      N α ε M₁ hα0 hα1 hε0 hgain hthresh H
  let L : ℕ := Nat.ceil A + Nat.ceil B
  refine ⟨L, ?_⟩
  intro n hn
  have hn1 : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hceilA : A ≤ (Nat.ceil A : ℝ) := Nat.le_ceil A
  have hceilB : B ≤ (Nat.ceil B : ℝ) := Nat.le_ceil B
  have hceilB0 : (0 : ℝ) ≤ (Nat.ceil B : ℝ) := Nat.cast_nonneg _
  have hreal : (f n : ℝ) ≤ ((L * n : ℕ) : ℝ) := by
    calc
      (f n : ℝ) ≤ A * n + B := hlin n
      _ ≤ ((Nat.ceil A : ℝ) + (Nat.ceil B : ℝ)) * n := by nlinarith
      _ = ((L * n : ℕ) : ℝ) := by simp [L, Nat.cast_add, Nat.cast_mul]
  exact_mod_cast hreal

/-- **The natural-number form consumed by Proposition 4.14.**  The affine real
bound from `linear_of_subdivision` can be rounded to one natural slope.  For
`n ≥ 1` the additive constant is absorbed into that slope, so no downstream
consumer has to repeat the real-to-natural bookkeeping. -/
theorem nat_linear_of_subdivision (f : ℕ → ℕ) (C : ℝ) (N : ℕ) (α : ℝ)
    (hC : 0 < C) (hα0 : 0 < α) (hα1 : α < 1)
    (H : ∀ n : ℕ, N < n → ∃ (k : ℕ) (m : Fin k → ℕ),
      (k : ℝ) ≤ C * Real.log n ∧
      (f n : ℝ) ≤ ∑ i, (f (m i) : ℝ) ∧
      (n : ℝ) ≤ ∑ i, (m i : ℝ) ∧
      (∑ i, (m i : ℝ)) ≤ (n : ℝ) + C * Real.log n ∧
      ∀ i, (m i : ℝ) ≤ α * n) :
    ∃ L : ℕ, ∀ n : ℕ, 1 ≤ n → f n ≤ L * n := by
  obtain ⟨A, B, hA, hB, hlin⟩ :=
    linear_of_subdivision f C N α hC hα0 hα1 H
  let L : ℕ := Nat.ceil A + Nat.ceil B
  refine ⟨L, ?_⟩
  intro n hn
  have hn0 : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg _
  have hn1 : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hceilA : A ≤ (Nat.ceil A : ℝ) := Nat.le_ceil A
  have hceilB : B ≤ (Nat.ceil B : ℝ) := Nat.le_ceil B
  have hceilB0 : (0 : ℝ) ≤ (Nat.ceil B : ℝ) := Nat.cast_nonneg _
  have hreal : (f n : ℝ) ≤ ((L * n : ℕ) : ℝ) := by
    calc
      (f n : ℝ) ≤ A * n + B := hlin n
      _ ≤ ((Nat.ceil A : ℝ) + (Nat.ceil B : ℝ)) * n := by nlinarith
      _ = ((L * n : ℕ) : ℝ) := by
        simp [L, Nat.cast_add, Nat.cast_mul]
  exact_mod_cast hreal

end DGO
end GroupApproximation
