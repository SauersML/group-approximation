import GroupApproximation.Manuscript.NonMFNotes.Full.RCFDecision.SturmTarskiParts.Local

/-!
# Sturm--Tarski, part 2: signed count of odd-order roots

`non_mf_group_notes.tex`, `thm:mf-arithmetic`, proof step "Fixed-dimensional
feasibility is decidable over the real closed field" (Tarski's decision
procedure, Basu--Pollack--Roy Thm 2.58).

A nonzero real polynomial `F` changes sign exactly at its roots of odd
multiplicity, from `-` to `+` when the local leading coefficient is positive.
Summing these signed crossings gives `(sgn F(+∞) - sgn F(-∞)) / 2`:

`two_mul_sum_oddj' : 2 * ∑_{F(x)=0} oddj x F = sgnTop F - sgnBot F`.

The proof is algebraic induction on the degree, splitting off the largest
root; the only analytic input is `sgn_eval_of_roots_lt` (Part 1).
-/

namespace GroupApproximation.Full.NN11b

namespace ST

open Polynomial

noncomputable section

/-- The signed crossing of `F` at `x`: `sgn (lc0 x F)` if `x` is a root of odd
multiplicity, else `0`. -/
def oddj (x : ℝ) (F : ℝ[X]) : ℤ := if Odd (rootMultiplicity x F) then sgn (lc0 x F) else 0

theorem oddj_of_not_root {x : ℝ} {F : ℝ[X]} (h : ¬F.IsRoot x) : oddj x F = 0 := by
  unfold oddj
  rw [rootMultiplicity_eq_zero h, if_neg Nat.not_odd_zero]

theorem two_mul_sum_oddj (n : ℕ) : ∀ F : ℝ[X], F.natDegree = n → F ≠ 0 →
    2 * ∑ x ∈ F.roots.toFinset, oddj x F = sgnTop F - sgnBot F := by
  refine Nat.strong_induction_on n ?_
  intro n ih F hn hF
  by_cases hr : ∃ y, F.IsRoot y
  · obtain ⟨y0, hy0⟩ := hr
    have hs : F.roots.toFinset.Nonempty :=
      ⟨y0, Multiset.mem_toFinset.mpr ((mem_roots hF).mpr hy0)⟩
    obtain ⟨x, hxs, hxmax⟩ : ∃ x ∈ F.roots.toFinset, ∀ y ∈ F.roots.toFinset, y ≤ x :=
      ⟨F.roots.toFinset.max' hs, Finset.max'_mem _ _, fun y hy => Finset.le_max' _ y hy⟩
    have hxr : F.IsRoot x := (mem_roots hF).mp (Multiset.mem_toFinset.mp hxs)
    obtain ⟨m, G, hm, hFG, hG, hl⟩ := exists_decomp x hF
    have hm0 : 0 < m := by
      rw [← hm]
      exact (rootMultiplicity_pos hF).mpr hxr
    have hG0 : G ≠ 0 := fun h0 => hG (by rw [h0, eval_zero])
    have hpow0 : ((X - C x) ^ m : ℝ[X]) ≠ 0 := pow_ne_zero _ (X_sub_C_ne_zero x)
    have hdeg : F.natDegree = m + G.natDegree := by
      rw [hFG, natDegree_mul hpow0 hG0, natDegree_pow, natDegree_X_sub_C, mul_one]
    have hGlt : G.natDegree < n := by omega
    have ihG := ih G.natDegree hGlt G rfl hG0
    have hsub : G.roots.toFinset ⊆ F.roots.toFinset.erase x := by
      intro y hy
      have hyG : G.IsRoot y := (mem_roots hG0).mp (Multiset.mem_toFinset.mp hy)
      have hyx : y ≠ x := by
        intro h
        apply hG
        rw [← h]
        exact hyG
      refine Finset.mem_erase.mpr ⟨hyx, Multiset.mem_toFinset.mpr ((mem_roots hF).mpr ?_)⟩
      show eval y F = 0
      rw [hFG, eval_mul, show eval y G = 0 from hyG, mul_zero]
    have hflip : ∀ y ∈ F.roots.toFinset.erase x, oddj y F = (-1) ^ m * oddj y G := by
      intro y hy
      obtain ⟨hyx, hys⟩ := Finset.mem_erase.mp hy
      have hylt : y - x < 0 := by
        have h1 := hxmax y hys
        have h2 : y ≠ x := hyx
        have h3 : y < x := lt_of_le_of_ne h1 h2
        linarith
      obtain ⟨k, G1, hk, hGG1, hG1, hl1⟩ := exists_decomp y hG0
      have h2 : F = (X - C y) ^ k * ((X - C x) ^ m * G1) := by
        rw [hFG, hGG1]
        ring
      have h3 : eval y ((X - C x) ^ m * G1) = (y - x) ^ m * eval y G1 := by
        rw [eval_mul, eval_pow, eval_sub, eval_X, eval_C]
      have h4 : eval y ((X - C x) ^ m * G1) ≠ 0 := by
        rw [h3]
        exact mul_ne_zero (pow_ne_zero _ hylt.ne) hG1
      obtain ⟨h5, h6⟩ := of_decomp h2 h4
      unfold oddj
      rw [h5, h6, h3, ← hk, ← hl1, sgn_mul, sgn_pow, sgn_of_neg hylt]
      by_cases ho : Odd (rootMultiplicity y G)
      · rw [if_pos ho, if_pos ho]
      · rw [if_neg ho, if_neg ho, mul_zero]
    have hzero : ∀ y ∈ F.roots.toFinset.erase x, y ∉ G.roots.toFinset → oddj y G = 0 := by
      intro y _ hyn
      apply oddj_of_not_root
      intro hyr
      exact hyn (Multiset.mem_toFinset.mpr ((mem_roots hG0).mpr hyr))
    have hsumF : ∑ y ∈ F.roots.toFinset, oddj y F =
        oddj x F + (-1) ^ m * ∑ y ∈ G.roots.toFinset, oddj y G := by
      rw [← Finset.add_sum_erase _ _ hxs, Finset.sum_congr rfl hflip, ← Finset.mul_sum,
        Finset.sum_subset hsub hzero]
    have hsg : sgn (eval x G) = sgnTop G := by
      unfold sgnTop
      refine sgn_eval_of_roots_lt hG0 (fun y hy => ?_)
      have hyF0 : eval y F = 0 := by
        rw [hFG, eval_mul, show eval y G = 0 from hy, mul_zero]
      have hyF : y ∈ F.roots.toFinset := Multiset.mem_toFinset.mpr ((mem_roots hF).mpr hyF0)
      refine lt_of_le_of_ne (hxmax y hyF) ?_
      intro h
      apply hG
      rw [← h]
      exact hy
    have hox : oddj x F = if Odd m then sgnTop G else 0 := by
      unfold oddj
      rw [hm, hl, hsg]
    have htop : sgnTop F = sgnTop G := by
      unfold sgnTop
      rw [hFG, leadingCoeff_mul, ((monic_X_sub_C x).pow m).leadingCoeff, one_mul]
    have hbot : sgnBot F = (-1) ^ m * sgnBot G := by
      unfold sgnBot
      rw [hdeg, hFG, leadingCoeff_mul, ((monic_X_sub_C x).pow m).leadingCoeff, one_mul, pow_add,
        show G.leadingCoeff * ((-1) ^ m * (-1) ^ G.natDegree) =
          (-1) ^ m * (G.leadingCoeff * (-1) ^ G.natDegree) by ring,
        sgn_neg_one_pow_mul]
    rw [hsumF, hox, htop, hbot]
    by_cases ho : Odd m
    · rw [if_pos ho, ho.neg_one_pow]
      linarith
    · rw [if_neg ho, (Nat.not_odd_iff_even.mp ho).neg_one_pow]
      linarith
  · have hr' : ∀ y, ¬F.IsRoot y := fun y hy => hr ⟨y, hy⟩
    have hempty : F.roots.toFinset = ∅ := by
      apply Finset.eq_empty_of_forall_notMem
      intro y hy
      exact hr' y ((mem_roots hF).mp (Multiset.mem_toFinset.mp hy))
    rw [hempty, Finset.sum_empty, mul_zero, sgnTop_eq_sgnBot_of_no_roots hF hr', sub_self]

/-- Signed odd crossings: `2 * ∑_{F(x)=0} oddj x F = sgnTop F - sgnBot F`. -/
theorem two_mul_sum_oddj' {F : ℝ[X]} (hF : F ≠ 0) :
    2 * ∑ x ∈ F.roots.toFinset, oddj x F = sgnTop F - sgnBot F :=
  two_mul_sum_oddj F.natDegree F rfl hF

end

end ST

end GroupApproximation.Full.NN11b
