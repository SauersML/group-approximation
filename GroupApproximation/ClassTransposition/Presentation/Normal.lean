import GroupApproximation.ClassTransposition.Presentation.Inj

/-!
# `CT_P(ℤ)` is normalized by the image of `H P`

Kourovka 17.61 lane (research node `ct-p-z-is-finitely-presented-by-position-shifting`, §1; the
input `piecewise-canonical-permutations-are-transposition-products`).

Every element of the image of `evalH` maps an ordered partition with smooth moduli canonically
onto another (`evalH_eq_frac`). Such a map conjugates a class transposition over `P` into a
product of class transpositions over `P`: split both boxes finely enough that every piece lies in
a box of the partition (`swap_split`), and conjugate piece by piece (`conj_swap`).
-/

namespace GroupApproximation.ClassTransposition.Presentation

open GroupApproximation.Kourovka1759 Equiv Box

variable {P : Set ℕ}

/-! ### Smooth moduli -/

theorem smooth_of_isPN (hprime : ∀ p ∈ P' P, p.Prime) {m : ℤ} (h : IsPN P m) :
    IsSmoothModulus P m := by
  obtain ⟨l, hl, rfl⟩ := h
  intro p hp hd
  obtain ⟨a, ha, hpa⟩ := (Prime.dvd_prod_iff hp.prime).1 (Int.natCast_dvd_natCast.1 hd)
  rw [(Nat.prime_dvd_prime_iff_eq hp (hprime a (hl a ha))).1 hpa]
  exact hl a ha

theorem smooth_mul {a b : ℤ} (ha : IsSmoothModulus P a) (hb : IsSmoothModulus P b) :
    IsSmoothModulus P (a * b) := fun p hp hd => by
  rcases (Nat.prime_iff_prime_int.mp hp).dvd_or_dvd hd with h | h
  exacts [ha p hp h, hb p hp h]

theorem smooth_of_mul_left {a b : ℤ} (h : IsSmoothModulus P (a * b)) : IsSmoothModulus P a :=
  fun p hp hd => h p hp (Dvd.dvd.mul_right hd b)

/-- The comb is the realization of the comb path. -/
theorem real_tp : ∀ k, real (comb 1) (tp k) = comb (k + 1)
  | 0 => rfl
  | k + 1 => by
    rw [tp, real_append, real_tp k, comb_succ_tail (n := k + 1) (by omega)]
    rfl

theorem isPN_comb (hpos : ∀ p ∈ P' P, 2 ≤ p) (n : ℕ) : ∀ F ∈ comb (n + 1), IsPN P F.m := by
  rw [← real_tp]
  exact isPN_real_one hpos (valW_tp n)

/-! ### Swaps of adjacent boxes -/

theorem frac_swapAt {b : List Box} (hb : IsPart b) {k : ℕ} (hk : k + 1 < b.length) :
    ∃ (E F : Box) (h : E.Disj F), E ∈ b ∧ F ∈ b ∧ frac b (swapAt b k) = swap E F h := by
  obtain ⟨l, E, F, l', rfl, hl⟩ := exists_decomp2 b hk
  have hp := hb.1
  rw [List.pairwise_append] at hp
  obtain ⟨-, hp2, hl'⟩ := hp
  rw [List.pairwise_cons] at hp2
  obtain ⟨hE, hp4⟩ := hp2
  rw [List.pairwise_cons] at hp4
  obtain ⟨hF, -⟩ := hp4
  have hEF : E.Disj F := hE F List.mem_cons_self
  refine ⟨E, F, hEF, by simp, by simp, ?_⟩
  rw [← hl, swapAt_mid]
  refine (eq_frac hb ?_ (forall₂_append' ?_ (.cons (swap_canon hEF) (.cons (swap_canon' hEF) ?_)))).symm
  · have := isPart_swapAt hb l.length
    rwa [swapAt_mid] at this
  · exact List.forall₂_same.2 fun G hG => swap_canon_of_disj hEF
      (hl' G hG E List.mem_cons_self) (hl' G hG F (List.mem_cons_of_mem _ List.mem_cons_self))
  · exact List.forall₂_same.2 fun G hG => swap_canon_of_disj hEF
      (hE G (List.mem_cons_of_mem _ hG)).symm (hF G hG).symm

/-- A permutation canonical on two disjoint boxes maps them onto disjoint boxes. -/
theorem canon_disj {g : Perm ℤ} {A B A' B' : Box} (hA : CanonOn g A A') (hB : CanonOn g B B')
    (h : A.Disj B) : A'.Disj B' := by
  intro n ha hb
  obtain ⟨t, rfl⟩ := (A'.mem_iff n).1 ha
  obtain ⟨s, hs⟩ := (B'.mem_iff _).1 hb
  rw [← hA t, ← hB s] at hs
  have e := g.injective hs
  exact h _ (A.elt_mem t) (by rw [e]; exact B.elt_mem s)

/-! ### Conjugation -/

theorem conj_list_mem {G : Type*} [Group G] (S : Subgroup G) (g : G) :
    ∀ L : List G, (∀ x ∈ L, g * x * g⁻¹ ∈ S) → g * L.prod * g⁻¹ ∈ S
  | [], _ => by rw [List.prod_nil, mul_one, mul_inv_cancel]; exact S.one_mem
  | x :: L, h => by
    have e : g * (x :: L).prod * g⁻¹ = (g * x * g⁻¹) * (g * L.prod * g⁻¹) := by
      rw [List.prod_cons]; group
    rw [e]
    exact S.mul_mem (h x List.mem_cons_self)
      (conj_list_mem S g L fun y hy => h y (List.mem_cons_of_mem _ hy))

section Conj

variable (hprime : ∀ p ∈ P' P, p.Prime)
include hprime

/-- A permutation mapping an ordered partition with smooth moduli canonically onto another
conjugates a class transposition over `P` into `CT_P(ℤ)`. -/
theorem conj_swap_mem {R R' : List Box} (hR : IsPart R) (hR' : IsPart R')
    (hl : R'.length = R.length) (hs : ∀ F ∈ R, IsPN P F.m) (hs' : ∀ F ∈ R', IsPN P F.m)
    {A B : Box} (h : A.Disj B) (hA : Adm P A) (hB : Adm P B) :
    frac R' R * swap A B h * (frac R' R)⁻¹ ∈ classTranspositionGroupOver P := by
  have hcan := frac_canon hR' hR hl
  obtain ⟨lk, hlk, hk⟩ := isPN_mprod hs'
  obtain ⟨k, hkdef⟩ : ∃ k, k = lk.prod := ⟨_, rfl⟩
  rw [← hkdef] at hk
  have hk0 : 0 < k := by rw [hkdef]; exact List.prod_pos fun a ha => (hprime a (hlk a ha)).pos
  have hks : IsSmoothModulus P (k : ℤ) := smooth_of_isPN hprime ⟨lk, hlk, by rw [hkdef]⟩
  -- every `k`-child of a box lies in a box of `R'`, which `g` maps canonically
  have key : ∀ X : Box, Adm P X → ∀ j : Fin k, ∃ Y : Box, Adm P Y ∧
      CanonOn (frac R' R) (place X (child k j)) Y := by
    intro X hX j
    obtain ⟨E, hE, hmem⟩ := hR'.2 (place X (child k j)).r
    have hdv : E.m ∣ (place X (child k j)).m := by
      rw [place_m, child_m, ← hk]
      exact Dvd.dvd.mul_right (List.dvd_prod (List.mem_map.2 ⟨E, hE, rfl⟩)) _
    obtain ⟨Z, hZ⟩ := eq_place hmem hdv
    obtain ⟨F, hF, hEF⟩ := forall₂_exists_left hcan E hE
    have hZs : IsSmoothModulus P Z.m := by
      have h1 : IsSmoothModulus P (place X (child k j)).m := by
        rw [place_m, child_m]; exact smooth_mul hks hX
      rw [hZ, place_m] at h1
      exact smooth_of_mul_left h1
    refine ⟨place F Z, ?_, by rw [hZ]; exact hEF.place Z⟩
    show IsSmoothModulus P (place F Z).m
    rw [place_m]
    exact smooth_mul hZs (smooth_of_isPN hprime (hs F hF))
  rw [← swap_split h k hk0]
  refine conj_list_mem _ _ _ fun x hx => ?_
  obtain ⟨j, -, rfl⟩ := List.mem_map.1 hx
  obtain ⟨YA, hYA, cA⟩ := key A hA j
  obtain ⟨YB, hYB, cB⟩ := key B hB j
  have hd' := canon_disj cA cB (disj_place_of h)
  rw [kidSwap, conj_swap (disj_place_of h) hd' cA cB]
  exact Subgroup.subset_closure (isClassTranspositionOver_swap hd' hYA hYB)

end Conj

end GroupApproximation.ClassTransposition.Presentation
