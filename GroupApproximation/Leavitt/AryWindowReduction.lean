import GroupApproximation.Leavitt.AryGradingSpans
import GroupApproximation.Meta.AxiomGuard

/-!
# Window reduction at arbitrary arity

`Leavitt/LeavittWindowReduction.lean` is the first stage of the Laurent half of
the rose-graph `K₁` computation, over a **binary** Leavitt family: monomials are
graded by `|α| - |β|`, and the elementary corner move cuts the top of a degree
window down to `1` and raises its bottom up to `-1`, so every unit with a finite
monomial representation is congruent, modulo the stably elementary units, to a
unit with degrees in `[-1, 1]`.

This module is the same reduction over a `CompleteMatrixFamily A ι`, so it
applies to `L_k(1,d)` for every `d`.  It uses `AryGradingSpans.exists_corner_move`,
whose conclusion carries the complementary projection `1 - s_{i₀} t_{i₀}` where
the binary one carries `s₁t₁`; that is the only shape change, and it costs one
extra clause in `corner_terms_mem_span` (`1 - s_{i₀}t_{i₀}` has degree `0`, being
the difference of two degree-zero monomials).

## Where this leaves `ScalarReduction`

`MatrixDiagonalization.ScalarReduction (L_k(1,d))` is, after
`KOne/AryCentralUnitsAreScalars.lean`, the single remaining input of the printed
`K₁(L_k(1,d)) ≅ k^×/(k^×)^{d-1}` of `cor:leavitt-mf-quotient`.  With this module
it reduces, at every arity and exactly as at `d = 2`
(`KOne/ResidualReduction.lean`), to the narrow-window kill:

    every unit whose value has degrees in `[-1, 1]` lies in `centralClassGroup`.

`AryLeavitt.scalarReduction_of_narrowReduction` is that reduction.  The kill
itself is not proved here at any arity beyond two, where it is
`KOne/RefineLoopDischarge.lean`.

Note the receptacle: at `d = 2` the binary file lands in `stableUnits`, because
`K₁(L_k(1,2)) = 0` collapses `centralClassGroup` onto it.  At `d ≥ 3` that
collapse is false, so the statement below lands in `centralClassGroup`, which is
what `ScalarReduction` is about in the first place.
-/

namespace GroupApproximation
namespace CompleteMatrixFamily

open MatrixDiagonalization

variable {A : Type*} [Ring A] {ι : Type*} [Fintype ι] [DecidableEq ι]
variable (F : CompleteMatrixFamily A ι)

/-! ### Degree windows -/

/-- Monomials with degree `|α| - |β|` in the window `[lo, hi]`. -/
def degreeMonomials (lo hi : ℤ) : Set A :=
  {x | ∃ a b : List ι, lo ≤ (a.length : ℤ) - b.length ∧
    (a.length : ℤ) - b.length ≤ hi ∧ x = F.wordS a * F.wordT b}

theorem degreeMonomials_mono {lo lo' hi hi' : ℤ} (h1 : lo' ≤ lo)
    (h2 : hi ≤ hi') :
    F.degreeMonomials lo hi ⊆ F.degreeMonomials lo' hi' := by
  rintro x ⟨a, b, hl, hh, rfl⟩
  exact ⟨a, b, h1.trans hl, hh.trans h2, rfl⟩

section Windows

variable {k : Type*} [Field k] [Algebra k A]

theorem span_degreeMonomials_mono {lo lo' hi hi' : ℤ} (h1 : lo' ≤ lo)
    (h2 : hi ≤ hi') :
    Submodule.span k (F.degreeMonomials lo hi) ≤
      Submodule.span k (F.degreeMonomials lo' hi') :=
  Submodule.span_mono (F.degreeMonomials_mono h1 h2)

/-- Balanced monomials at any depth live in the zero window. -/
theorem span_levelMonomialSet_le_degree (n : ℕ) :
    Submodule.span k (F.levelMonomialSet n) ≤
      Submodule.span k (F.degreeMonomials 0 0) := by
  refine Submodule.span_mono ?_
  rw [levelMonomialSet_eq]
  rintro x ⟨a, b, ha, hb, rfl⟩
  exact ⟨a, b, by omega, by omega, rfl⟩

/-- The zero window is balanced: after padding, every degree-zero monomial has
both words of a common length. -/
theorem span_degree_zero_le_levelSpan {x : A}
    (hx : x ∈ Submodule.span k (F.degreeMonomials 0 0)) :
    ∃ n : ℕ, x ∈ Submodule.span k (F.levelMonomialSet n) := by
  induction hx using Submodule.span_induction with
  | mem x hxmem =>
      obtain ⟨a, b, hl, hh, rfl⟩ := hxmem
      have hlen : a.length = b.length := by omega
      exact ⟨a.length, F.monomial_mem_span_levelMonomialSet (k := k) a.length
        rfl hlen.symm⟩
  | zero => exact ⟨0, Submodule.zero_mem _⟩
  | add x y _ _ hx hy =>
      obtain ⟨m, hm⟩ := hx
      obtain ⟨n, hn⟩ := hy
      exact ⟨max m n, Submodule.add_mem _
        (F.span_levelMonomialSet_mono (le_max_left m n) hm)
        (F.span_levelMonomialSet_mono (le_max_right m n) hn)⟩
  | smul r x _ hx =>
      obtain ⟨n, hn⟩ := hx
      exact ⟨n, Submodule.smul_mem _ r hn⟩

/-- Wrapping a window element between single letters preserves the window. -/
theorem wrap_mem_span {lo hi : ℤ} (i j : ι) {x : A}
    (hx : x ∈ Submodule.span k (F.degreeMonomials lo hi)) :
    F.left i * x * F.right j ∈
      Submodule.span k (F.degreeMonomials lo hi) := by
  induction hx using Submodule.span_induction with
  | mem x hxmem =>
      obtain ⟨a, b, hl, hh, rfl⟩ := hxmem
      refine Submodule.subset_span ⟨i :: a, j :: b, ?_, ?_, ?_⟩
      · simpa using hl
      · simpa using hh
      · rw [F.wordS_cons, F.wordT_cons]
        noncomm_ring
  | zero =>
      rw [mul_zero, zero_mul]
      exact Submodule.zero_mem _
  | add x y _ _ hx hy =>
      rw [mul_add, add_mul]
      exact Submodule.add_mem _ hx hy
  | smul r x _ hx =>
      rw [mul_smul_comm, smul_mul_assoc]
      exact Submodule.smul_mem _ r hx

/-- Split off the positive part as a right factor of `s_{i₀}`. -/
theorem exists_decomp_top (i₀ : ι) {lo hi : ℤ} {x : A}
    (hx : x ∈ Submodule.span k (F.degreeMonomials lo hi)) :
    ∃ a b : A, x = a + b * F.left i₀ ∧
      a ∈ Submodule.span k (F.degreeMonomials lo 0) ∧
      b ∈ Submodule.span k (F.degreeMonomials 0 (hi - 1)) := by
  induction hx using Submodule.span_induction with
  | mem x hxmem =>
      obtain ⟨a, b, hl, hh, rfl⟩ := hxmem
      by_cases hd : (a.length : ℤ) - b.length ≤ 0
      · exact ⟨F.wordS a * F.wordT b, 0, by rw [zero_mul, add_zero],
          Submodule.subset_span ⟨a, b, hl, hd, rfl⟩, Submodule.zero_mem _⟩
      · refine ⟨0, F.wordS a * F.wordT (i₀ :: b), ?_, Submodule.zero_mem _,
          Submodule.subset_span ⟨a, i₀ :: b, ?_, ?_, rfl⟩⟩
        · rw [zero_add]
          exact F.monomial_factor_left i₀ a b
        · simp only [List.length_cons]
          push_cast
          omega
        · simp only [List.length_cons]
          push_cast
          omega
  | zero =>
      exact ⟨0, 0, by rw [zero_mul, add_zero], Submodule.zero_mem _,
        Submodule.zero_mem _⟩
  | add x y _ _ hx hy =>
      obtain ⟨ax, bx, hxe, hax, hbx⟩ := hx
      obtain ⟨ay, by', hye, hay, hby⟩ := hy
      exact ⟨ax + ay, bx + by', by rw [hxe, hye, add_mul]; abel,
        Submodule.add_mem _ hax hay, Submodule.add_mem _ hbx hby⟩
  | smul r x _ hx =>
      obtain ⟨a, b, hxe, ha, hb⟩ := hx
      exact ⟨r • a, r • b, by rw [hxe, smul_add, smul_mul_assoc],
        Submodule.smul_mem _ r ha, Submodule.smul_mem _ r hb⟩

/-- Split off the negative part as a left factor of `t_{i₀}`. -/
theorem exists_decomp_bot (i₀ : ι) {lo hi : ℤ} {x : A}
    (hx : x ∈ Submodule.span k (F.degreeMonomials lo hi)) :
    ∃ c r : A, x = F.right i₀ * c + r ∧
      c ∈ Submodule.span k (F.degreeMonomials (lo + 1) 0) ∧
      r ∈ Submodule.span k (F.degreeMonomials 0 hi) := by
  induction hx using Submodule.span_induction with
  | mem x hxmem =>
      obtain ⟨a, b, hl, hh, rfl⟩ := hxmem
      by_cases hd : 0 ≤ (a.length : ℤ) - b.length
      · exact ⟨0, F.wordS a * F.wordT b, by rw [mul_zero, zero_add],
          Submodule.zero_mem _, Submodule.subset_span ⟨a, b, hd, hh, rfl⟩⟩
      · refine ⟨F.wordS (i₀ :: a) * F.wordT b, 0, ?_,
          Submodule.subset_span ⟨i₀ :: a, b, ?_, ?_, rfl⟩,
          Submodule.zero_mem _⟩
        · rw [add_zero]
          exact F.monomial_factor_right i₀ a b
        · simp only [List.length_cons]
          push_cast
          omega
        · simp only [List.length_cons]
          push_cast
          omega
  | zero =>
      exact ⟨0, 0, by rw [mul_zero, add_zero], Submodule.zero_mem _,
        Submodule.zero_mem _⟩
  | add x y _ _ hx hy =>
      obtain ⟨cx, rx, hxe, hcx, hrx⟩ := hx
      obtain ⟨cy, ry, hye, hcy, hry⟩ := hy
      exact ⟨cx + cy, rx + ry, by rw [hxe, hye, mul_add]; abel,
        Submodule.add_mem _ hcx hcy, Submodule.add_mem _ hrx hry⟩
  | smul r x _ hx =>
      obtain ⟨c, r', hxe, hc, hr⟩ := hx
      exact ⟨r • c, r • r', by rw [hxe, smul_add, mul_smul_comm],
        Submodule.smul_mem _ r hc, Submodule.smul_mem _ r hr⟩

/-- The three universal correction terms of the corner move.  The third is the
complementary projection, which is a difference of two degree-zero monomials
rather than a single one --- the only place the arity shows. -/
theorem corner_terms_mem_span (i₀ i₁ : ι) {lo hi : ℤ} (hlo : lo ≤ -1)
    (hhi : 1 ≤ hi) :
    F.left i₁ * F.left i₀ * F.right i₀ ∈
        Submodule.span k (F.degreeMonomials lo hi) ∧
      F.left i₀ * F.right i₀ * F.right i₁ ∈
        Submodule.span k (F.degreeMonomials lo hi) ∧
      (1 - F.left i₀ * F.right i₀) ∈
        Submodule.span k (F.degreeMonomials lo hi) := by
  refine ⟨Submodule.subset_span ⟨[i₁, i₀], [i₀], ?_, ?_, ?_⟩,
    Submodule.subset_span ⟨[i₀], [i₁, i₀], ?_, ?_, ?_⟩,
    Submodule.sub_mem _ (Submodule.subset_span ⟨[], [], ?_, ?_, ?_⟩)
      (Submodule.subset_span ⟨[i₀], [i₀], ?_, ?_, ?_⟩)⟩
  · simp; omega
  · simp; omega
  · show F.left i₁ * F.left i₀ * F.right i₀ = F.wordS [i₁, i₀] * F.wordT [i₀]
    simp [mul_assoc]
  · simp; omega
  · simp; omega
  · show F.left i₀ * F.right i₀ * F.right i₁ = F.wordS [i₀] * F.wordT [i₁, i₀]
    simp [mul_assoc]
  · simp; omega
  · simp; omega
  · simp
  · simp; omega
  · simp; omega
  · show F.left i₀ * F.right i₀ = F.wordS [i₀] * F.wordT [i₀]
    simp

/-- One corner move cuts the top of the window by one. -/
theorem exists_top_cut [Nontrivial A]
    (hdiv : ∀ x : A, x ≠ 0 → ∃ p q : A, p * x * q = 1)
    {i₀ i₁ : ι} (hne : i₀ ≠ i₁) {lo hi : ℤ} (hlo : lo ≤ -1) (hhi : 2 ≤ hi)
    (u : Aˣ) (hu : (u : A) ∈ Submodule.span k (F.degreeMonomials lo hi)) :
    ∃ u' : Aˣ, u' * u⁻¹ ∈ stableUnits A ∧
      (u' : A) ∈ Submodule.span k (F.degreeMonomials lo (hi - 1)) := by
  obtain ⟨a, b, hxe, ha, hb⟩ := F.exists_decomp_top i₀ hu
  obtain ⟨u', hval, hmem⟩ := F.exists_corner_move hdiv hne u (-b) (F.left i₀)
  refine ⟨u', hmem, ?_⟩
  have huvw : (u : A) + -b * F.left i₀ = a := by
    rw [hxe, neg_mul]; abel
  rw [hval, huvw]
  obtain ⟨hterm1, -, hterm3⟩ :=
    F.corner_terms_mem_span (k := k) i₀ i₁ hlo (by omega : (1 : ℤ) ≤ hi - 1)
  refine Submodule.add_mem _ (Submodule.add_mem _ (Submodule.add_mem _
    ?_ ?_) ?_) hterm3
  · exact F.wrap_mem_span i₀ i₀
      (F.span_degreeMonomials_mono le_rfl (by omega) ha)
  · exact F.wrap_mem_span i₀ i₁ (Submodule.neg_mem _
      (F.span_degreeMonomials_mono (by omega) le_rfl hb))
  · exact hterm1

/-- One mirror corner move raises the bottom of the window by one. -/
theorem exists_bot_cut [Nontrivial A]
    (hdiv : ∀ x : A, x ≠ 0 → ∃ p q : A, p * x * q = 1)
    {i₀ i₁ : ι} (hne : i₀ ≠ i₁) {lo hi : ℤ} (hlo : lo ≤ -2) (hhi : 1 ≤ hi)
    (u : Aˣ) (hu : (u : A) ∈ Submodule.span k (F.degreeMonomials lo hi)) :
    ∃ u' : Aˣ, u' * u⁻¹ ∈ stableUnits A ∧
      (u' : A) ∈ Submodule.span k (F.degreeMonomials (lo + 1) hi) := by
  obtain ⟨c, r, hxe, hc, hr⟩ := F.exists_decomp_bot i₀ hu
  obtain ⟨u', hval, hmem⟩ := F.exists_corner_move hdiv hne u (F.right i₀) (-c)
  refine ⟨u', hmem, ?_⟩
  have huvw : (u : A) + F.right i₀ * -c = r := by
    rw [hxe, mul_neg]; abel
  rw [hval, huvw]
  obtain ⟨hterm1, hterm2, hterm3⟩ :=
    F.corner_terms_mem_span (k := k) i₀ i₁
      (by omega : lo + 1 ≤ -1) (by omega : (1 : ℤ) ≤ hi)
  refine Submodule.add_mem _ (Submodule.add_mem _ (Submodule.add_mem _
    ?_ ?_) ?_) hterm3
  · exact F.wrap_mem_span i₀ i₀
      (F.span_degreeMonomials_mono (by omega) le_rfl hr)
  · exact hterm2
  · exact F.wrap_mem_span i₁ i₀ (Submodule.neg_mem _
      (F.span_degreeMonomials_mono le_rfl (by omega) hc))

/-- **Window reduction at arbitrary arity**: every unit with value in a finite
degree window is congruent, modulo the stably elementary units, to a unit with
degrees in `[-1, 1]`. -/
theorem exists_window_reduction [Nontrivial A]
    (hdiv : ∀ x : A, x ≠ 0 → ∃ p q : A, p * x * q = 1)
    {i₀ i₁ : ι} (hne : i₀ ≠ i₁) {lo hi : ℤ} (u : Aˣ)
    (hu : (u : A) ∈ Submodule.span k (F.degreeMonomials lo hi)) :
    ∃ u' : Aˣ, u' * u⁻¹ ∈ stableUnits A ∧
      (u' : A) ∈ Submodule.span k (F.degreeMonomials (-1) 1) := by
  have hwide : (u : A) ∈ Submodule.span k
      (F.degreeMonomials (min lo (-1)) (max hi 1)) :=
    F.span_degreeMonomials_mono (min_le_left _ _) (le_max_left _ _) hu
  clear hu
  set lo' := min lo (-1) with hlo'
  set hi' := max hi 1 with hhi'
  have hlo : lo' ≤ -1 := min_le_right _ _
  have hhi : 1 ≤ hi' := le_max_right _ _
  clear_value lo' hi'
  clear hlo' hhi'
  -- first cut the top down to 1
  obtain ⟨u₁, hmem₁, hu₁⟩ : ∃ u' : Aˣ, u' * u⁻¹ ∈ stableUnits A ∧
      (u' : A) ∈ Submodule.span k (F.degreeMonomials lo' 1) := by
    obtain ⟨n, hn⟩ : ∃ n : ℕ, hi' = 1 + n := ⟨(hi' - 1).toNat, by omega⟩
    subst hn
    clear hhi
    induction n generalizing u with
    | zero =>
        refine ⟨u, by rw [mul_inv_cancel]; exact one_mem _, ?_⟩
        rwa [show (1 : ℤ) + ((0 : ℕ) : ℤ) = 1 from by simp] at hwide
    | succ m ih =>
        obtain ⟨u₁, hmem₁, hu₁⟩ :=
          F.exists_top_cut hdiv hne hlo (by omega) u hwide
        obtain ⟨u₂, hmem₂, hu₂⟩ := ih u₁ (by
          simp only [Nat.cast_add, Nat.cast_one] at hu₁
          rwa [show (1 : ℤ) + ((m : ℤ) + 1) - 1 = 1 + (m : ℤ) from by
            ring] at hu₁)
        refine ⟨u₂, ?_, hu₂⟩
        have := mul_mem hmem₂ hmem₁
        rwa [show u₂ * u₁⁻¹ * (u₁ * u⁻¹) = u₂ * u⁻¹ from by group] at this
  -- then raise the bottom up to -1
  obtain ⟨u₂, hmem₂, hu₂⟩ : ∃ u' : Aˣ, u' * u₁⁻¹ ∈ stableUnits A ∧
      (u' : A) ∈ Submodule.span k (F.degreeMonomials (-1) 1) := by
    obtain ⟨n, hn⟩ : ∃ n : ℕ, lo' = -1 - n := ⟨(-1 - lo').toNat, by omega⟩
    subst hn
    clear hlo hwide
    induction n generalizing u₁ with
    | zero =>
        refine ⟨u₁, by rw [mul_inv_cancel]; exact one_mem _, ?_⟩
        rwa [show (-1 : ℤ) - ((0 : ℕ) : ℤ) = -1 from by simp] at hu₁
    | succ m ih =>
        obtain ⟨v₁, hvmem, hv₁⟩ :=
          F.exists_bot_cut hdiv hne (by omega) (by omega) u₁ hu₁
        have hv₁u : v₁ * u⁻¹ ∈ stableUnits A := by
          have hchain := mul_mem hvmem hmem₁
          rwa [show v₁ * u₁⁻¹ * (u₁ * u⁻¹) = v₁ * u⁻¹ from by group] at hchain
        have hv₁' : (v₁ : A) ∈ Submodule.span k
            (F.degreeMonomials (-1 - (m : ℤ)) 1) := by
          simp only [Nat.cast_add, Nat.cast_one] at hv₁
          rwa [show (-1 : ℤ) - ((m : ℤ) + 1) + 1 = -1 - (m : ℤ) from by
            ring] at hv₁
        obtain ⟨v₂, hv2mem, hv₂⟩ := ih v₁ hv₁u hv₁'
        refine ⟨v₂, ?_, hv₂⟩
        have := mul_mem hv2mem hvmem
        rwa [show v₂ * v₁⁻¹ * (v₁ * u₁⁻¹) = v₂ * u₁⁻¹ from by group] at this
  refine ⟨u₂, ?_, hu₂⟩
  have := mul_mem hmem₂ hmem₁
  rwa [show u₂ * u₁⁻¹ * (u₁ * u⁻¹) = u₂ * u⁻¹ from by group] at this

end Windows

end CompleteMatrixFamily

/-! ### The Leavitt specialisation -/

namespace AryLeavitt

open MatrixDiagonalization CompleteMatrixFamily

variable (k : Type) [Field k] (d : ℕ)

/-- Every element of `L_k(1,d)` lies in a finite degree window. -/
theorem exists_mem_span_degreeMonomials (x : AryLeavittAlgebra k d) :
    ∃ lo hi : ℤ,
      x ∈ Submodule.span k ((family k d).degreeMonomials lo hi) := by
  have hx : x ∈ Submodule.span k (monomialSet k d) := by
    rw [span_monomialSet_eq_top]
    exact Submodule.mem_top
  induction hx using Submodule.span_induction with
  | mem x hxmem =>
      obtain ⟨a, b, rfl⟩ := hxmem
      exact ⟨(a.length : ℤ) - b.length, (a.length : ℤ) - b.length,
        Submodule.subset_span ⟨a, b, le_rfl, le_rfl, rfl⟩⟩
  | zero => exact ⟨0, 0, Submodule.zero_mem _⟩
  | add x y _ _ hx hy =>
      obtain ⟨lox, hix, hmx⟩ := hx
      obtain ⟨loy, hiy, hmy⟩ := hy
      exact ⟨min lox loy, max hix hiy, Submodule.add_mem _
        ((family k d).span_degreeMonomials_mono (min_le_left _ _)
          (le_max_left _ _) hmx)
        ((family k d).span_degreeMonomials_mono (min_le_right _ _)
          (le_max_right _ _) hmy)⟩
  | smul r x _ hx =>
      obtain ⟨lo, hi, hm⟩ := hx
      exact ⟨lo, hi, Submodule.smul_mem _ r hm⟩

/-- **Narrow representatives at every arity**: every unit of `L_k(1,d)` is
congruent, modulo the stably elementary units, to a unit with degrees in
`[-1, 1]`. -/
theorem exists_narrow_representative (hd : 2 ≤ d)
    (u : (AryLeavittAlgebra k d)ˣ) :
    ∃ u' : (AryLeavittAlgebra k d)ˣ,
      u' * u⁻¹ ∈ stableUnits (AryLeavittAlgebra k d) ∧
      ((u' : (AryLeavittAlgebra k d)ˣ) : AryLeavittAlgebra k d) ∈
        Submodule.span k ((family k d).degreeMonomials (-1) 1) := by
  haveI : NeZero d := ⟨by omega⟩
  obtain ⟨lo, hi, hm⟩ := exists_mem_span_degreeMonomials k d
    ((u : (AryLeavittAlgebra k d)ˣ) : AryLeavittAlgebra k d)
  have hne : (⟨0, by omega⟩ : Fin d) ≠ ⟨1, by omega⟩ := by
    simp only [ne_eq, Fin.mk.injEq]
    omega
  exact (family k d).exists_window_reduction
    (fun x hx ↦ exists_mul_mul_eq_one k d hd hx) hne u hm

/-- **The narrow-window kill statement at arity `d`**: every unit whose value
lies in the degree window `[-1, 1]` is a central scalar modulo the stably
elementary units. -/
def NarrowReduction : Prop :=
  ∀ u : (AryLeavittAlgebra k d)ˣ,
    ((u : (AryLeavittAlgebra k d)ˣ) : AryLeavittAlgebra k d) ∈
      Submodule.span k ((family k d).degreeMonomials (-1) 1) →
    u ∈ centralClassGroup (AryLeavittAlgebra k d)

/-- **Positive control**: a balanced unit satisfies the narrow-window
conclusion, at every arity.  This is the degree-zero half of
`AryDegreeZeroUnits`, and it is where a proof of `NarrowReduction` would have to
start. -/
theorem narrowReduction_of_levelSpan (hd : 2 ≤ d) (n : ℕ)
    (u : (AryLeavittAlgebra k d)ˣ)
    (hu : ((u : (AryLeavittAlgebra k d)ˣ) : AryLeavittAlgebra k d) ∈
      Submodule.span k ((family k d).levelMonomialSet n)) :
    u ∈ centralClassGroup (AryLeavittAlgebra k d) :=
  mem_centralClassGroup_of_val_mem_levelSpan k d hd n u hu

/-- **The chain**: the narrow-window kill implies the rose-graph input
`ScalarReduction (L_k(1,d))`, at every arity.

This is `KOne/ResidualReduction.lean`'s reduction, ported.  The only difference
is the receptacle: at `d = 2` the binary file can land in `stableUnits`, because
`K₁(L_k(1,2)) = 0`; at `d ≥ 3` that collapse is false, so both the hypothesis
and the conclusion are stated with `centralClassGroup`, which is what
`ScalarReduction` means. -/
theorem scalarReduction_of_narrowReduction (hd : 2 ≤ d)
    (hnarrow : NarrowReduction k d) :
    ScalarReduction (AryLeavittAlgebra k d) := by
  refine scalarReduction_of_forall_mem_centralClassGroup ?_
  intro u
  obtain ⟨u', hmem, hval⟩ := exists_narrow_representative k d hd u
  have hu' : u' ∈ centralClassGroup (AryLeavittAlgebra k d) := hnarrow u' hval
  have hH : u' * u⁻¹ ∈ centralClassGroup (AryLeavittAlgebra k d) :=
    stableUnits_le_centralClassGroup hmem
  have hres := mul_mem (inv_mem hH) hu'
  rwa [show (u' * u⁻¹)⁻¹ * u' = u from by group] at hres

end AryLeavitt
end GroupApproximation

/-! ### Axiom audit -/

#audit_axioms GroupApproximation.CompleteMatrixFamily.wrap_mem_span
#audit_axioms GroupApproximation.CompleteMatrixFamily.corner_terms_mem_span
#audit_axioms GroupApproximation.CompleteMatrixFamily.exists_top_cut
#audit_axioms GroupApproximation.CompleteMatrixFamily.exists_bot_cut
#audit_axioms GroupApproximation.CompleteMatrixFamily.exists_window_reduction
#audit_axioms GroupApproximation.AryLeavitt.exists_narrow_representative
#audit_axioms GroupApproximation.AryLeavitt.scalarReduction_of_narrowReduction
