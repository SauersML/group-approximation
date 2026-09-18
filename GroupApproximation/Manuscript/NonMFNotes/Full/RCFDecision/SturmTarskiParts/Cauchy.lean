import GroupApproximation.Manuscript.NonMFNotes.Full.RCFDecision.SturmTarskiParts.OddRoots

/-!
# Sturm--Tarski, part 3: the algebraic Cauchy index

`non_mf_group_notes.tex`, `thm:mf-arithmetic`, proof step "Fixed-dimensional
feasibility is decidable over the real closed field" (Tarski's decision
procedure; Basu--Pollack--Roy, Prop 2.55 and Thm 2.57).

For nonzero `A`, `B` the Cauchy index of `B / A` is the sum over the roots of `A`
of the jump `jmp x A B`: at a pole of `B / A` of odd order, the sign of the local
leading coefficient.  We prove:

* `cind_swap`: `Ind(B/A) + Ind(A/B) = Var_{-∞}(A, B) - Var_{+∞}(A, B)`
  (Basu--Pollack--Roy Thm 2.57, via `two_mul_sum_oddj'` applied to `A * B`);
* `cind_rel`: if `c A + d D = S B` with `c, d > 0`, then `Ind(A/B) = -Ind(D/B)`;
* `cind_of_dvd`: if `B ∣ A` then `Ind(A/B) = 0`.
-/

namespace GroupApproximation.Full.NN11b

namespace ST

open Polynomial

noncomputable section

/-- The jump of `B / A` at `x`. -/
def jmp (x : ℝ) (A B : ℝ[X]) : ℤ :=
  if rootMultiplicity x B < rootMultiplicity x A ∧
      Odd (rootMultiplicity x A - rootMultiplicity x B) then
    sgn (lc0 x A * lc0 x B)
  else 0

/-- The (algebraic) Cauchy index of `B / A`. -/
def cind (A B : ℝ[X]) : ℤ := ∑ x ∈ A.roots.toFinset, jmp x A B

theorem jmp_of_not_root {x : ℝ} {A B : ℝ[X]} (h : ¬A.IsRoot x) : jmp x A B = 0 := by
  unfold jmp
  rw [rootMultiplicity_eq_zero h]
  have hn : ¬(rootMultiplicity x B < 0 ∧ Odd (0 - rootMultiplicity x B)) :=
    fun hc => Nat.not_lt_zero _ hc.1
  rw [if_neg hn]

theorem odd_sub_iff_odd_add {a b : ℕ} (h : b < a) : Odd (a - b) ↔ Odd (a + b) := by
  rw [Nat.odd_iff, Nat.odd_iff]
  constructor
  · intro h1
    omega
  · intro h1
    omega

theorem jmp_aux (a b : ℕ) (s : ℤ) :
    ((if b < a ∧ Odd (a - b) then s else 0) + (if a < b ∧ Odd (b - a) then s else 0)) =
      if Odd (a + b) then s else 0 := by
  rcases lt_trichotomy a b with h | h | h
  · have hn : ¬(b < a ∧ Odd (a - b)) := fun hc => absurd hc.1 (by omega)
    rw [if_neg hn, zero_add]
    by_cases ho : Odd (b - a)
    · have h2 : a < b ∧ Odd (b - a) := ⟨h, ho⟩
      have h3 : Odd (a + b) := by
        rw [add_comm]
        exact (odd_sub_iff_odd_add h).mp ho
      rw [if_pos h2, if_pos h3]
    · have h2 : ¬(a < b ∧ Odd (b - a)) := fun hc => ho hc.2
      have h3 : ¬Odd (a + b) := by
        intro hc
        apply ho
        refine (odd_sub_iff_odd_add h).mpr ?_
        rw [add_comm]
        exact hc
      rw [if_neg h2, if_neg h3]
  · have hn1 : ¬(b < a ∧ Odd (a - b)) := fun hc => absurd hc.1 (by omega)
    have hn2 : ¬(a < b ∧ Odd (b - a)) := fun hc => absurd hc.1 (by omega)
    have h3 : ¬Odd (a + b) := by
      intro hc
      rw [Nat.odd_iff] at hc
      omega
    rw [if_neg hn1, if_neg hn2, if_neg h3, add_zero]
  · have hn : ¬(a < b ∧ Odd (b - a)) := fun hc => absurd hc.1 (by omega)
    rw [if_neg hn, add_zero]
    by_cases ho : Odd (a - b)
    · have h2 : b < a ∧ Odd (a - b) := ⟨h, ho⟩
      have h3 : Odd (a + b) := (odd_sub_iff_odd_add h).mp ho
      rw [if_pos h2, if_pos h3]
    · have h2 : ¬(b < a ∧ Odd (a - b)) := fun hc => ho hc.2
      have h3 : ¬Odd (a + b) := fun hc => ho ((odd_sub_iff_odd_add h).mpr hc)
      rw [if_neg h2, if_neg h3]

/-- Pointwise: the jumps of `B/A` and `A/B` add up to the odd crossing of `A * B`. -/
theorem jmp_add_jmp (x : ℝ) {A B : ℝ[X]} (hA : A ≠ 0) (hB : B ≠ 0) :
    jmp x A B + jmp x B A = oddj x (A * B) := by
  have key := jmp_aux (rootMultiplicity x A) (rootMultiplicity x B) (sgn (lc0 x A * lc0 x B))
  obtain ⟨h1, h2⟩ := mu_lc0_mul x hA hB
  unfold jmp oddj
  rw [h1, h2, mul_comm (lc0 x B) (lc0 x A)]
  exact key

theorem roots_subset_mul_left {A B : ℝ[X]} (hAB : A * B ≠ 0) :
    A.roots.toFinset ⊆ (A * B).roots.toFinset := by
  intro y hy
  have hA : A ≠ 0 := left_ne_zero_of_mul hAB
  have hyA : A.IsRoot y := (mem_roots hA).mp (Multiset.mem_toFinset.mp hy)
  refine Multiset.mem_toFinset.mpr ((mem_roots hAB).mpr ?_)
  show eval y (A * B) = 0
  rw [eval_mul, show eval y A = 0 from hyA, zero_mul]

theorem roots_subset_mul_right {A B : ℝ[X]} (hAB : A * B ≠ 0) :
    B.roots.toFinset ⊆ (A * B).roots.toFinset := by
  intro y hy
  have hB : B ≠ 0 := right_ne_zero_of_mul hAB
  have hyB : B.IsRoot y := (mem_roots hB).mp (Multiset.mem_toFinset.mp hy)
  refine Multiset.mem_toFinset.mpr ((mem_roots hAB).mpr ?_)
  show eval y (A * B) = 0
  rw [eval_mul, show eval y B = 0 from hyB, mul_zero]

/-- `cind A B` as a sum over any finite set containing the roots of `A`. -/
theorem cind_eq_sum_of_subset {A B : ℝ[X]} (hA : A ≠ 0) {s : Finset ℝ}
    (hs : A.roots.toFinset ⊆ s) : cind A B = ∑ x ∈ s, jmp x A B := by
  unfold cind
  have hz : ∀ y ∈ s, y ∉ A.roots.toFinset → jmp y A B = 0 := by
    intro y _ hy
    apply jmp_of_not_root
    intro hr
    exact hy (Multiset.mem_toFinset.mpr ((mem_roots hA).mpr hr))
  exact Finset.sum_subset hs hz

theorem cind_add_cind {A B : ℝ[X]} (hA : A ≠ 0) (hB : B ≠ 0) :
    cind A B + cind B A = ∑ x ∈ (A * B).roots.toFinset, oddj x (A * B) := by
  have hAB : A * B ≠ 0 := mul_ne_zero hA hB
  rw [cind_eq_sum_of_subset hA (roots_subset_mul_left hAB),
    cind_eq_sum_of_subset hB (roots_subset_mul_right hAB), ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl (fun y _ => jmp_add_jmp y hA hB)

theorem sgnTop_mul (A B : ℝ[X]) : sgnTop (A * B) = sgnTop A * sgnTop B := by
  unfold sgnTop
  rw [leadingCoeff_mul, sgn_mul]

theorem sgnBot_mul {A B : ℝ[X]} (hA : A ≠ 0) (hB : B ≠ 0) :
    sgnBot (A * B) = sgnBot A * sgnBot B := by
  unfold sgnBot
  rw [leadingCoeff_mul, natDegree_mul hA hB, pow_add, ← sgn_mul,
    show A.leadingCoeff * B.leadingCoeff * ((-1) ^ A.natDegree * (-1) ^ B.natDegree) =
      A.leadingCoeff * (-1) ^ A.natDegree * (B.leadingCoeff * (-1) ^ B.natDegree) by ring]

theorem sgnTop_cases {A : ℝ[X]} (hA : A ≠ 0) : sgnTop A = 1 ∨ sgnTop A = -1 :=
  sgn_cases (leadingCoeff_ne_zero.mpr hA)

theorem sgnBot_cases {A : ℝ[X]} (hA : A ≠ 0) : sgnBot A = 1 ∨ sgnBot A = -1 := by
  have h : A.leadingCoeff * (-1 : ℝ) ^ A.natDegree ≠ 0 :=
    mul_ne_zero (leadingCoeff_ne_zero.mpr hA) (pow_ne_zero _ (neg_ne_zero.mpr one_ne_zero))
  exact sgn_cases h

theorem two_mul_changes_pair {a b : ℤ} (ha : a = 1 ∨ a = -1) (hb : b = 1 ∨ b = -1) :
    2 * ((changes [a, b] : ℕ) : ℤ) = 1 - a * b := by
  rcases ha with rfl | rfl <;> rcases hb with rfl | rfl <;> decide

/-- Basu--Pollack--Roy Thm 2.57 for two nonzero polynomials. -/
theorem cind_swap {A B : ℝ[X]} (hA : A ≠ 0) (hB : B ≠ 0) :
    cind A B + cind B A =
      ((changes [sgnBot A, sgnBot B] : ℕ) : ℤ) - ((changes [sgnTop A, sgnTop B] : ℕ) : ℤ) := by
  have h1 := two_mul_sum_oddj' (mul_ne_zero hA hB)
  rw [sgnTop_mul, sgnBot_mul hA hB] at h1
  have hc := cind_add_cind hA hB
  have e1 := two_mul_changes_pair (sgnBot_cases hA) (sgnBot_cases hB)
  have e2 := two_mul_changes_pair (sgnTop_cases hA) (sgnTop_cases hB)
  linarith

theorem cind_of_dvd {A B : ℝ[X]} (hB : B ≠ 0) (hA : A ≠ 0) (hdvd : B ∣ A) : cind B A = 0 := by
  obtain ⟨E, hE⟩ := hdvd
  have hE0 : E ≠ 0 := by
    intro h0
    apply hA
    rw [hE, h0, mul_zero]
  unfold cind
  refine Finset.sum_eq_zero (fun x _ => ?_)
  have hm : rootMultiplicity x A = rootMultiplicity x B + rootMultiplicity x E := by
    rw [hE]
    exact (mu_lc0_mul x hB hE0).1
  have hn : ¬(rootMultiplicity x A < rootMultiplicity x B ∧
      Odd (rootMultiplicity x B - rootMultiplicity x A)) := by
    intro hc
    have h1 := hc.1
    omega
  unfold jmp
  rw [if_neg hn]

theorem sgn_neg (a : ℝ) : sgn (-a) = -sgn a := by
  rw [show -a = (-1) ^ 1 * a by ring, sgn_neg_one_pow_mul, pow_one, neg_one_mul]

/-- Pointwise form of `cind_rel`. -/
theorem jmp_rel (x : ℝ) {A B D S : ℝ[X]} (hA : A ≠ 0) (_hB : B ≠ 0) (hD : D ≠ 0) {c d : ℝ}
    (hc : 0 < c) (hd : 0 < d) (hrel : C c * A + C d * D = S * B) :
    jmp x B A = -jmp x B D := by
  have hCA : C c * A ≠ 0 := mul_ne_zero (C_ne_zero.mpr hc.ne') hA
  have hCD : C d * D ≠ 0 := mul_ne_zero (C_ne_zero.mpr hd.ne') hD
  have hdvdSB : (X - C x) ^ rootMultiplicity x B ∣ S * B :=
    dvd_mul_of_dvd_right (pow_rootMultiplicity_dvd B x) S
  obtain ⟨kA1, kA2⟩ := mu_lc0_C_mul hc.ne' x hA
  obtain ⟨kD1, kD2⟩ := mu_lc0_C_mul hd.ne' x hD
  by_cases hAl : rootMultiplicity x A < rootMultiplicity x B
  · have hdvd : (X - C x) ^ rootMultiplicity x B ∣ C c * A + C d * D := by
      rw [hrel]
      exact hdvdSB
    have hlt : rootMultiplicity x (C c * A) < rootMultiplicity x B := by
      rw [kA1]
      exact hAl
    obtain ⟨g1, g2⟩ := mu_lc0_of_dvd_add (rootMultiplicity x B) hCA hlt hdvd
    rw [kD1, kA1] at g1
    rw [kD2, kA2] at g2
    have hs : sgn (lc0 x D) = -sgn (lc0 x A) := by
      have k1 : sgn (d * lc0 x D) = sgn (lc0 x D) := by
        rw [sgn_mul, sgn_of_pos hd, one_mul]
      have k2 : sgn (-(c * lc0 x A)) = -sgn (lc0 x A) := by
        rw [sgn_neg, sgn_mul, sgn_of_pos hc, one_mul]
      rw [← k1, g2, k2]
    unfold jmp
    rw [g1, sgn_mul (lc0 x B) (lc0 x A), sgn_mul (lc0 x B) (lc0 x D), hs]
    by_cases hcond : rootMultiplicity x A < rootMultiplicity x B ∧
        Odd (rootMultiplicity x B - rootMultiplicity x A)
    · rw [if_pos hcond, if_pos hcond, mul_neg, neg_neg]
    · rw [if_neg hcond, if_neg hcond, neg_zero]
  · have hDl : ¬rootMultiplicity x D < rootMultiplicity x B := by
      intro hlt
      have hdvd' : (X - C x) ^ rootMultiplicity x B ∣ C d * D + C c * A := by
        rw [add_comm, hrel]
        exact hdvdSB
      have hlt' : rootMultiplicity x (C d * D) < rootMultiplicity x B := by
        rw [kD1]
        exact hlt
      have g := (mu_lc0_of_dvd_add (rootMultiplicity x B) hCD hlt' hdvd').1
      rw [kA1, kD1] at g
      apply hAl
      rw [g]
      exact hlt
    have n1 : ¬(rootMultiplicity x A < rootMultiplicity x B ∧
        Odd (rootMultiplicity x B - rootMultiplicity x A)) := fun h => hAl h.1
    have n2 : ¬(rootMultiplicity x D < rootMultiplicity x B ∧
        Odd (rootMultiplicity x B - rootMultiplicity x D)) := fun h => hDl h.1
    unfold jmp
    rw [if_neg n1, if_neg n2, neg_zero]

/-- A remainder relation `c A + d D = S B` (`c, d > 0`) negates the Cauchy index. -/
theorem cind_rel {A B D S : ℝ[X]} (hA : A ≠ 0) (hB : B ≠ 0) (hD : D ≠ 0) {c d : ℝ}
    (hc : 0 < c) (hd : 0 < d) (hrel : C c * A + C d * D = S * B) :
    cind B A + cind B D = 0 := by
  unfold cind
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_eq_zero (fun x _ => ?_)
  have h := jmp_rel x hA hB hD hc hd hrel
  linarith

end

end ST

end GroupApproximation.Full.NN11b
