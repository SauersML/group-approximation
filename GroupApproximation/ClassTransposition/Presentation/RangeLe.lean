import GroupApproximation.ClassTransposition.Presentation.Normal

/-!
# The image of `evalH` lies in `CT_P(ℤ)`

Kourovka 17.61 lane (research node `ct-p-z-is-finitely-presented-by-position-shifting`, §1; the
input `piecewise-canonical-permutations-are-transposition-products`, Lemma 7).

`NH` is the subgroup of `H P` evaluating into `CT_P(ℤ)`. It is normal (`conj_mem`). It contains:
* every swap (a class transposition of two comb boxes);
* every binary split (relation (d) at the tail: `ρ · 1 = X₂ · swaps`).
For an odd `p ∈ P`, modulo `NH` relation (d) at the tail gives `X_p(j) ≡ Y_p(j+1)`, relation (c)
with `q = 2` at the tail gives `Y_p(j) ≡ X_p(j) · Y_p(j+p)`, and the shift gives
`Y_p(m) ≡ Y_p(2)` for `m ≥ 2`. So `Y_p(2) ≡ Y_p(2)²`, and every generator lies in `NH`.
-/

namespace GroupApproximation.ClassTransposition.Presentation

open GroupApproximation.Kourovka1759 Equiv Box

variable {P : Set ℕ}

/-- The elements of `H P` evaluating into `CT_P(ℤ)`. -/
def NH (hpos : ∀ p ∈ P' P, 2 ≤ p) (hP2 : 2 ∉ P) : Subgroup (H P) :=
  (classTranspositionGroupOver P).comap (evalH hpos hP2)

theorem hatH_swap_out {k n : ℕ} (h : ¬ k + 1 < n) : hatH P (.swap k) n = 1 := by
  have e : hatF P (.swap k) n = 1 := by
    simp only [hatF, if_neg (show ¬ k + 2 < n by omega), if_neg (show ¬ k + 2 = n by omega)]
  rw [hatH, e, map_one]

theorem hatH_split_two_out {i n : ℕ} (h : ¬ i + 1 < n) : hatH P (.split i 2) n = 1 := by
  have e : hatF P (.split i 2) n = 1 := by
    simp only [hatF, if_neg h, if_neg (show ¬ (i + 1 = n ∧ (2 : ℕ) ≠ 2) by simp)]
  rw [hatH, e, map_one]

theorem layer_two (j p : ℕ) : layer j 2 p = [.split j p, .split (j + p) p] := by
  rw [layer, show List.range 2 = [0, 1] from rfl]
  simp

section Le

variable (hB : BddAbove (P' P)) (hP2 : 2 ∉ P) (hpos : ∀ p ∈ P' P, 2 ≤ p)
  (hprime : ∀ p ∈ P' P, p.Prime)
include hB hP2 hpos hprime

theorem evalH_eq_frac (h : H P) : ∃ R R' : List Box, IsPart R ∧ IsPart R' ∧
    R'.length = R.length ∧ (∀ F ∈ R, IsPN P F.m) ∧ (∀ F ∈ R', IsPN P F.m) ∧
    evalH hpos hP2 h = frac R' R := by
  obtain ⟨a, a', ha, ha', hl, rfl⟩ := mem_fracSet hB hP2 hpos hprime h
  have hc := isPart_comb (levW 1 a') (by have := levW_ge 1 a' (ValW.ok hpos ha'); omega)
  have hRa := isPart_real (isPart_comb 1 one_pos) a (ValW.ok hpos ha)
  have hRa' := isPart_real (isPart_comb 1 one_pos) a' (ValW.ok hpos ha')
  have l1 : (comb (levW 1 a')).length = (real (comb 1) a).length := by
    rw [length_comb, length_real, length_comb, hl]
  have l2 : (comb (levW 1 a')).length = (real (comb 1) a').length := by
    rw [length_comb, length_real, length_comb]
  refine ⟨real (comb 1) a, real (comb 1) a', hRa, hRa', by rw [← l2, ← l1],
    isPN_real_one hpos ha, isPN_real_one hpos ha', ?_⟩
  rw [map_mul, map_inv, evalH_toH hpos hP2 one_pos ha, evalH_toH hpos hP2 one_pos ha', hl,
    frac_inv hc hRa' l2, frac_mul hRa' hc hRa l2.symm l1]

/-- `CT_P(ℤ)` is normalized by the image of `evalH`. -/
theorem conj_mem (h : H P) {x : Perm ℤ} (hx : x ∈ classTranspositionGroupOver P) :
    evalH hpos hP2 h * x * (evalH hpos hP2 h)⁻¹ ∈ classTranspositionGroupOver P := by
  obtain ⟨R, R', hR, hR', hl, hs, hs', he⟩ := evalH_eq_frac hB hP2 hpos hprime h
  rw [he]
  rw [classTranspositionGroupOver] at hx
  induction hx using Subgroup.closure_induction with
  | mem y hy =>
    obtain ⟨A, B, hAB, hA, hB', rfl⟩ := IsClassTranspositionOver.eq_swap hy
    exact conj_swap_mem hprime hR hR' hl hs hs' hAB hA hB'
  | one => rw [mul_one, mul_inv_cancel]; exact Subgroup.one_mem _
  | mul y z _ _ hy hz =>
    have e : frac R' R * (y * z) * (frac R' R)⁻¹ =
        (frac R' R * y * (frac R' R)⁻¹) * (frac R' R * z * (frac R' R)⁻¹) := by group
    rw [e]; exact Subgroup.mul_mem _ hy hz
  | inv y _ hy =>
    have e : frac R' R * y⁻¹ * (frac R' R)⁻¹ = (frac R' R * y * (frac R' R)⁻¹)⁻¹ := by group
    rw [e]; exact Subgroup.inv_mem _ hy

theorem nh_normal : (NH hpos hP2).Normal :=
  ⟨fun n hn h => by
    show evalH hpos hP2 (h * n * h⁻¹) ∈ classTranspositionGroupOver P
    rw [map_mul, map_mul, map_inv]
    exact conj_mem hB hP2 hpos hprime h hn⟩

omit hB in
theorem swap_mem_nh (k n : ℕ) : hatH P (.swap k) n ∈ NH hpos hP2 := by
  by_cases hk : k + 1 < n
  · obtain ⟨n, rfl⟩ : ∃ n', n = n' + 1 := ⟨n - 1, by omega⟩
    show evalH hpos hP2 (hatH P (.swap k) (n + 1)) ∈ classTranspositionGroupOver P
    rw [← toH_single, evalH_toH hpos hP2 (by omega) (show ValW P (n + 1) [.swap k] from ⟨hk, trivial⟩)]
    show frac (comb (n + 1)) (swapAt (comb (n + 1)) k) ∈ _
    obtain ⟨E, F, hEF, hE, hF, he⟩ :=
      frac_swapAt (isPart_comb (n + 1) (by omega)) (by rw [length_comb]; exact hk)
    rw [he]
    exact Subgroup.subset_closure (isClassTranspositionOver_swap hEF
      (smooth_of_isPN hprime (isPN_comb hpos n E hE)) (smooth_of_isPN hprime (isPN_comb hpos n F hF)))
  · rw [hatH_swap_out hk]; exact Subgroup.one_mem _

omit hB in
theorem swaps_mem_nh (n i : ℕ) : ∀ w : List ℕ, toH P n (swaps i w) ∈ NH hpos hP2
  | [] => by rw [show swaps i [] = [] from rfl, toH_nil]; exact Subgroup.one_mem _
  | k :: w => by
    rw [show swaps i (k :: w) = .swap (i + k) :: swaps i w from rfl, toH_cons, lev_swap]
    exact Subgroup.mul_mem _ (swap_mem_nh hP2 hpos hprime _ _) (swaps_mem_nh n i w)

theorem two_mem_nh (j : ℕ) (h2 : 2 ∈ P' P) : gH (tX 2 h2) (j + 1) ∈ NH hpos hP2 := by
  have e := dk1_all hB h2 (j + 2) j (by omega)
  rw [toH_cons, lev_swap, toH_single, hatH_split_tail_two (show j + 1 + 1 = j + 2 by omega),
    mul_one, toH_cons, hatH_split_front (show j + 1 < j + 2 by omega) h2] at e
  rw [eq_mul_inv_of_mul_eq e.symm]
  exact Subgroup.mul_mem _ (swap_mem_nh hP2 hpos hprime _ _)
    (Subgroup.inv_mem _ (swaps_mem_nh hP2 hpos hprime _ _ _))

theorem split_two_mem_nh (i n : ℕ) : hatH P (.split i 2) n ∈ NH hpos hP2 := by
  by_cases h : i + 1 < n
  · rw [hatH_split_front h (two_mem P)]; exact two_mem_nh hB hP2 hpos hprime i _
  · rw [hatH_split_two_out h]; exact Subgroup.one_mem _

/-- Words of swaps and binary splits lie in `NH`. -/
theorem cheap_mem_nh : ∀ (w : List Move) (n : ℕ),
    (∀ m ∈ w, (∃ k, m = .swap k) ∨ (∃ i, m = .split i 2)) → toH P n w ∈ NH hpos hP2
  | [], n, _ => by rw [toH_nil]; exact Subgroup.one_mem _
  | m :: w, n, h => by
    rw [toH_cons]
    refine Subgroup.mul_mem _ ?_ (cheap_mem_nh w _ fun m' hm' => h m' (List.mem_cons_of_mem _ hm'))
    rcases h m List.mem_cons_self with ⟨k, rfl⟩ | ⟨i, rfl⟩
    · exact swap_mem_nh hP2 hpos hprime k n
    · exact split_two_mem_nh hB hP2 hpos hprime i n

end Le

end GroupApproximation.ClassTransposition.Presentation
