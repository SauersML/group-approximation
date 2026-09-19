import GroupApproximation.Kourovka2175.Basic
import GroupApproximation.Kourovka2175.Arith

/-!
# Kourovka Notebook Problem 21.75, answered negatively

Research nodes: `ct-p1-and-ct-p2-generate-ct-of-the-union` and its proof route
`ct-p1-and-ct-p2-generate-ct-of-the-union-proof`.

For any two sets `P₁`, `P₂` of odd primes, `CT_{P₁}(ℤ)` and `CT_{P₂}(ℤ)` generate
`CT_{P₁ ∪ P₂}(ℤ)` (`kourovka_21_75`). The proof follows the route with one simplification:
no normalization by `CT_∅` is needed.

1. Split a generating swap into the swaps of its `4`-children, so both moduli are `4K`, `4L`.
2. Two disjoint classes are separated by a prime power `p ^ k` dividing both moduli
   (`sep_prime`). Put `Q` for the one of `P₁, P₂` with `p ∈ {2} ∪ Q` and `Q'` for the other.
3. Split `K = K₁ K₂` with `K₁` the `{2} ∪ Q`-part, and likewise `L`. The shadows
   `SA = a(4K₁) ⊇ A` and `SB = b(4L₁) ⊇ B` are disjoint, because `p ^ k ∣ 4K₁, 4L₁`.
4. Pick residues `z₁ ≠ z₂` mod `4` avoiding `a` and `b` mod `4`, and put `U = x(8)`,
   `V = (x+4)(8)` with `x = a mod 4`. A swap in `CT_{Q'}` moves `U, V` into sub-boxes of
   `z₁(4), z₂(4)`, and a swap in `CT_Q` moves those onto `A, B`. The composite `σ` is canonical
   `U → A` and `V → B`, so `swap A B = σ · swap U V · σ⁻¹`.
-/

namespace GroupApproximation.Kourovka2175

open GroupApproximation.Kourovka1759
open GroupApproximation.Kourovka1759.Box

/-- Elements of a box whose modulus is divisible by `4` have the residue of the box mod `4`. -/
theorem mod_four_of_mem {C : Box} (h4 : (4 : ℤ) ∣ C.m) {n : ℤ} (hn : C.Mem n) :
    n % 4 = C.r % 4 := by
  have hn' : n % C.m = C.r := hn
  rw [← Int.emod_emod_of_dvd n h4, hn']

theorem disj_of_mod_four {C D : Box} {c d : ℤ} (hC : ∀ n, C.Mem n → n % 4 = c)
    (hD : ∀ n, D.Mem n → n % 4 = d) (hcd : c ≠ d) : C.Disj D :=
  fun n hc hd => hcd ((hC n hc).symm.trans (hD n hd))

/-- A prime power of a prime in `R` that divides `4 (K₁ K₂)` divides `4 K₁` when `K₂` has no
prime factor in `R`. -/
theorem dvd_four_part {R : Set ℕ} {p k : ℕ} (hp : p.Prime) (hpR : p ∈ R) {K₁ K₂ M : ℤ}
    (hM : M = 4 * K₁ * K₂) (hK₂ : ∀ q : ℕ, q.Prime → (q : ℤ) ∣ K₂ → q ∉ R)
    (hpM : (p : ℤ) ^ k ∣ M) : (p : ℤ) ^ k ∣ 4 * K₁ := by
  have hcop : IsCoprime ((p : ℤ) ^ k) K₂ :=
    (isCoprime_prime_of_not_dvd hp fun hd => hK₂ p hp hd hpR).pow_left
  apply hcop.dvd_of_dvd_mul_right
  rw [← hM]
  exact hpM

/-- The `Q'`-part of a modulus: the prime factors of `K₂` lie in `Q'`. -/
theorem smooth_copart {Q Q' : Set ℕ} {K K₁ K₂ : ℤ} (hKe : K = K₁ * K₂)
    (hsK : ∀ q : ℕ, q.Prime → (q : ℤ) ∣ K → q = 2 ∨ q ∈ Q ∨ q ∈ Q')
    (hK₂ : ∀ q : ℕ, q.Prime → (q : ℤ) ∣ K₂ → q ∉ insert 2 Q) : IsSmoothModulus Q' K₂ := by
  intro q hq hd
  have hnot := hK₂ q hq hd
  have hqK : (q : ℤ) ∣ K := by rw [hKe]; exact dvd_mul_of_dvd_right hd K₁
  rcases hsK q hq hqK with h2 | hQq | hQ'q
  · exact absurd (Set.mem_insert_iff.2 (Or.inl h2)) hnot
  · exact absurd (Set.mem_insert_iff.2 (Or.inr hQq)) hnot
  · exact Or.inr hQ'q

/-- The transport step. Let `A`, `B` be disjoint boxes with moduli `4K`, `4L` whose prime
factors lie in `{2} ∪ Q ∪ Q'`, separated by a power of a prime of `{2} ∪ Q`. Then the swap of
`A` and `B` lies in every subgroup containing `CT_Q` and `CT_{Q'}`. -/
theorem swap_mem_of_sep {Q Q' : Set ℕ} {H : Subgroup (Equiv.Perm ℤ)}
    (hQ : classTranspositionGroupOver Q ≤ H) (hQ' : classTranspositionGroupOver Q' ≤ H)
    {A B : Box} (h : A.Disj B) {K L : ℤ} (hK : 0 < K) (hL : 0 < L)
    (hAm : A.m = 4 * K) (hBm : B.m = 4 * L)
    (hsK : ∀ q : ℕ, q.Prime → (q : ℤ) ∣ K → q = 2 ∨ q ∈ Q ∨ q ∈ Q')
    (hsL : ∀ q : ℕ, q.Prime → (q : ℤ) ∣ L → q = 2 ∨ q ∈ Q ∨ q ∈ Q')
    {p k : ℕ} (hp : p.Prime) (hpQ : p = 2 ∨ p ∈ Q) (hpA : (p : ℤ) ^ k ∣ A.m)
    (hpB : (p : ℤ) ^ k ∣ B.m) (hpab : ¬ (p : ℤ) ^ k ∣ A.r - B.r) :
    swap A B h ∈ H := by
  obtain ⟨K₁, K₂, hK₁, -, hKe, hK₁R, hK₂R⟩ := int_split (insert 2 Q) K hK
  obtain ⟨L₁, L₂, hL₁, -, hLe, hL₁R, hL₂R⟩ := int_split (insert 2 Q) L hL
  have hpR : p ∈ insert 2 Q := Set.mem_insert_iff.2 hpQ
  have sK₁ : IsSmoothModulus Q (4 * K₁) :=
    (isSmoothModulus_four Q).mul fun q hq hd => Set.mem_insert_iff.1 (hK₁R q hq hd)
  have sL₁ : IsSmoothModulus Q (4 * L₁) :=
    (isSmoothModulus_four Q).mul fun q hq hd => Set.mem_insert_iff.1 (hL₁R q hq hd)
  have sK₂ : IsSmoothModulus Q' K₂ := smooth_copart hKe hsK hK₂R
  have sL₂ : IsSmoothModulus Q' L₂ := smooth_copart hLe hsL hL₂R
  have hM₁ : (p : ℤ) ^ k ∣ 4 * K₁ :=
    dvd_four_part hp hpR (by rw [hAm, hKe]; ring) hK₂R hpA
  have hN₁ : (p : ℤ) ^ k ∣ 4 * L₁ :=
    dvd_four_part hp hpR (by rw [hBm, hLe]; ring) hL₂R hpB
  have h4K₁ : (0 : ℤ) < 4 * K₁ := mul_pos (by norm_num) hK₁
  have h4L₁ : (0 : ℤ) < 4 * L₁ := mul_pos (by norm_num) hL₁
  have hAm' : A.m = K₂ * (4 * K₁) := by rw [hAm, hKe]; ring
  have hBm' : B.m = L₂ * (4 * L₁) := by rw [hBm, hLe]; ring
  -- the shadows `SA ⊇ A`, `SB ⊇ B` and the boxes `E`, `F` with `A = place SA E`, `B = place SB F`
  obtain ⟨SA, hSAr, hSAm⟩ : ∃ SA : Box, SA.r = A.r % (4 * K₁) ∧ SA.m = 4 * K₁ :=
    ⟨⟨A.r % (4 * K₁), 4 * K₁, Int.emod_nonneg _ h4K₁.ne', Int.emod_lt_of_pos _ h4K₁⟩, rfl, rfl⟩
  obtain ⟨SB, hSBr, hSBm⟩ : ∃ SB : Box, SB.r = B.r % (4 * L₁) ∧ SB.m = 4 * L₁ :=
    ⟨⟨B.r % (4 * L₁), 4 * L₁, Int.emod_nonneg _ h4L₁.ne', Int.emod_lt_of_pos _ h4L₁⟩, rfl, rfl⟩
  obtain ⟨E, hEr, hEm⟩ : ∃ E : Box, E.r = A.r / (4 * K₁) ∧ E.m = K₂ :=
    ⟨⟨A.r / (4 * K₁), K₂, Int.ediv_nonneg A.hr h4K₁.le,
      Int.ediv_lt_of_lt_mul h4K₁ (by rw [← hAm']; exact A.hrm)⟩, rfl, rfl⟩
  obtain ⟨F, hFr, hFm⟩ : ∃ F : Box, F.r = B.r / (4 * L₁) ∧ F.m = L₂ :=
    ⟨⟨B.r / (4 * L₁), L₂, Int.ediv_nonneg B.hr h4L₁.le,
      Int.ediv_lt_of_lt_mul h4L₁ (by rw [← hBm']; exact B.hrm)⟩, rfl, rfl⟩
  have hAeq : place SA E = A := by
    ext
    · rw [place_r, hSAr, hEr, hSAm]
      linear_combination Int.emod_add_ediv_mul A.r (4 * K₁)
    · rw [place_m, hEm, hSAm, hAm']
  have hBeq : place SB F = B := by
    ext
    · rw [place_r, hSBr, hFr, hSBm]
      linear_combination Int.emod_add_ediv_mul B.r (4 * L₁)
    · rw [place_m, hFm, hSBm, hBm']
  -- residues mod `4`
  obtain ⟨x, hxA⟩ : ∃ x, x = A.r % 4 := ⟨_, rfl⟩
  obtain ⟨y, hyB⟩ : ∃ y, y = B.r % 4 := ⟨_, rfl⟩
  have hx0 : 0 ≤ x := by omega
  have hx4 : x < 4 := by omega
  have hy0 : 0 ≤ y := by omega
  have hy4 : y < 4 := by omega
  obtain ⟨z₁, z₂, hz₁0, hz₁4, hz₂0, hz₂4, hz12, hz1x, hz1y, hz2x, hz2y⟩ :=
    exists_two_avoid x y hx0 hx4 hy0 hy4
  obtain ⟨U, hUr, hUm⟩ : ∃ U : Box, U.r = x ∧ U.m = 8 := ⟨⟨x, 8, hx0, by omega⟩, rfl, rfl⟩
  obtain ⟨V, hVr, hVm⟩ : ∃ V : Box, V.r = x + 4 ∧ V.m = 8 :=
    ⟨⟨x + 4, 8, by omega, by omega⟩, rfl, rfl⟩
  obtain ⟨U₁, hU₁r, hU₁m⟩ : ∃ U₁ : Box, U₁.r = z₁ ∧ U₁.m = 4 :=
    ⟨⟨z₁, 4, hz₁0, hz₁4⟩, rfl, rfl⟩
  obtain ⟨V₁, hV₁r, hV₁m⟩ : ∃ V₁ : Box, V₁.r = z₂ ∧ V₁.m = 4 :=
    ⟨⟨z₂, 4, hz₂0, hz₂4⟩, rfl, rfl⟩
  have rU : ∀ n, U.Mem n → n % 4 = x := by
    intro n hn
    have hn' : n % U.m = U.r := hn
    rw [hUm, hUr] at hn'
    omega
  have rV : ∀ n, V.Mem n → n % 4 = x := by
    intro n hn
    have hn' : n % V.m = V.r := hn
    rw [hVm, hVr] at hn'
    omega
  have rU₁ : ∀ n, U₁.Mem n → n % 4 = z₁ := by
    intro n hn
    have hn' : n % U₁.m = U₁.r := hn
    rw [hU₁m, hU₁r] at hn'
    exact hn'
  have rV₁ : ∀ n, V₁.Mem n → n % 4 = z₂ := by
    intro n hn
    have hn' : n % V₁.m = V₁.r := hn
    rw [hV₁m, hV₁r] at hn'
    exact hn'
  have rSA : ∀ n, SA.Mem n → n % 4 = x := by
    intro n hn
    rw [mod_four_of_mem (by rw [hSAm]; exact dvd_mul_right 4 K₁) hn, hSAr, hxA]
    exact Int.emod_emod_of_dvd _ (dvd_mul_right 4 K₁)
  have rSB : ∀ n, SB.Mem n → n % 4 = y := by
    intro n hn
    rw [mod_four_of_mem (by rw [hSBm]; exact dvd_mul_right 4 L₁) hn, hSBr, hyB]
    exact Int.emod_emod_of_dvd _ (dvd_mul_right 4 L₁)
  have rX : ∀ n, (place U₁ E).Mem n → n % 4 = z₁ := fun n hn => rU₁ n (place_mem_of hn)
  have rY : ∀ n, (place V₁ F).Mem n → n % 4 = z₂ := fun n hn => rV₁ n (place_mem_of hn)
  have rPB : ∀ n, (place SB F).Mem n → n % 4 = y := fun n hn => rSB n (place_mem_of hn)
  -- disjointness
  have hUV : U.Disj V := by
    intro n h1 h2
    have e1 : n % U.m = U.r := h1
    have e2 : n % V.m = V.r := h2
    rw [hUm, hUr] at e1
    rw [hVm, hVr] at e2
    omega
  have hUX : U.Disj (place U₁ E) := disj_of_mod_four rU rX (Ne.symm hz1x)
  have hVY : V.Disj (place V₁ F) := disj_of_mod_four rV rY (Ne.symm hz2x)
  have hUY : U.Disj (place V₁ F) := disj_of_mod_four rU rY (Ne.symm hz2x)
  have hYX : (place V₁ F).Disj (place U₁ E) := disj_of_mod_four rY rX (Ne.symm hz12)
  have hU₁SA : U₁.Disj SA := disj_of_mod_four rU₁ rSA hz1x
  have hV₁SB : V₁.Disj SB := disj_of_mod_four rV₁ rSB hz2y
  have hXV₁ : (place U₁ E).Disj V₁ := disj_of_mod_four rX rV₁ hz12
  have hXSB : (place U₁ E).Disj SB := disj_of_mod_four rX rSB hz1y
  have hPBU₁ : (place SB F).Disj U₁ := disj_of_mod_four rPB rU₁ (Ne.symm hz1y)
  have hSAB : SA.Disj SB := by
    intro n h1 h2
    have e1 : n % SA.m = SA.r := h1
    have e2 : n % SB.m = SB.r := h2
    rw [hSAm, hSAr] at e1
    rw [hSBm, hSBr] at e2
    have d1 : 4 * K₁ ∣ A.r - n := Int.ModEq.dvd (show Int.ModEq (4 * K₁) n A.r from e1)
    have d2 : 4 * L₁ ∣ B.r - n := Int.ModEq.dvd (show Int.ModEq (4 * L₁) n B.r from e2)
    apply hpab
    have hd := dvd_sub (hM₁.trans d1) (hN₁.trans d2)
    rwa [show A.r - n - (B.r - n) = A.r - B.r by ring] at hd
  have hPBSA : (place SB F).Disj SA := fun n h1 h2 => hSAB n h2 (place_mem_of h1)
  -- the swaps and the groups they lie in
  have mUX : swap U (place U₁ E) hUX ∈ classTranspositionGroupOver Q' :=
    swap_mem_over hUX (by rw [hUm]; exact isSmoothModulus_eight Q')
      (by rw [place_m, hEm, hU₁m]; exact sK₂.mul (isSmoothModulus_four Q'))
  have mVY : swap V (place V₁ F) hVY ∈ classTranspositionGroupOver Q' :=
    swap_mem_over hVY (by rw [hVm]; exact isSmoothModulus_eight Q')
      (by rw [place_m, hFm, hV₁m]; exact sL₂.mul (isSmoothModulus_four Q'))
  have mU₁SA : swap U₁ SA hU₁SA ∈ classTranspositionGroupOver Q :=
    swap_mem_over hU₁SA (by rw [hU₁m]; exact isSmoothModulus_four Q) (by rw [hSAm]; exact sK₁)
  have mV₁SB : swap V₁ SB hV₁SB ∈ classTranspositionGroupOver Q :=
    swap_mem_over hV₁SB (by rw [hV₁m]; exact isSmoothModulus_four Q) (by rw [hSBm]; exact sL₁)
  have mUV : swap U V hUV ∈ classTranspositionGroupOver Q :=
    swap_mem_over hUV (by rw [hUm]; exact isSmoothModulus_eight Q)
      (by rw [hVm]; exact isSmoothModulus_eight Q)
  -- canonical maps
  have c₂U : CanonOn (swap U (place U₁ E) hUX * swap V (place V₁ F) hVY) U (place U₁ E) :=
    (swap_canon_of_disj hVY hUV hUY).comp (swap_canon hUX)
  have c₂V : CanonOn (swap U (place U₁ E) hUX * swap V (place V₁ F) hVY) V (place V₁ F) :=
    (swap_canon hVY).comp (swap_canon_of_disj hUX hUY.symm hYX)
  have c₁X : CanonOn (swap U₁ SA hU₁SA * swap V₁ SB hV₁SB) (place U₁ E) A := by
    have hc := (swap_canon_of_disj hV₁SB hXV₁ hXSB).comp ((swap_canon hU₁SA).place E)
    rwa [hAeq] at hc
  have c₁Y : CanonOn (swap U₁ SA hU₁SA * swap V₁ SB hV₁SB) (place V₁ F) B := by
    have hc := ((swap_canon hV₁SB).place F).comp (swap_canon_of_disj hU₁SA hPBU₁ hPBSA)
    rwa [hBeq] at hc
  have key := conj_swap hUV h (c₂U.comp c₁X) (c₂V.comp c₁Y)
  rw [← key]
  have hg₁ : swap U₁ SA hU₁SA * swap V₁ SB hV₁SB ∈ H := hQ (mul_mem mU₁SA mV₁SB)
  have hg₂ : swap U (place U₁ E) hUX * swap V (place V₁ F) hVY ∈ H := hQ' (mul_mem mUX mVY)
  have hσ := mul_mem hg₁ hg₂
  exact mul_mem (mul_mem hσ (hQ mUV)) (inv_mem hσ)

/-- A swap of two disjoint boxes with moduli `4K`, `4L` over `P₁ ∪ P₂` lies in
`⟨CT_{P₁}, CT_{P₂}⟩`. -/
theorem swap_mem_sup_of_four {P₁ P₂ : Set ℕ} {A B : Box} (h : A.Disj B) {K L : ℤ}
    (hK : 0 < K) (hL : 0 < L) (hAm : A.m = 4 * K) (hBm : B.m = 4 * L)
    (hsK : IsSmoothModulus (P₁ ∪ P₂) K) (hsL : IsSmoothModulus (P₁ ∪ P₂) L) :
    swap A B h ∈ classTranspositionGroupOver P₁ ⊔ classTranspositionGroupOver P₂ := by
  have hdisj : ∀ n : ℤ, (∃ t, n = A.r + t * A.m) → (∃ t, n = B.r + t * B.m) → False :=
    fun n ha hb => h n ((A.mem_iff n).2 ha) ((B.mem_iff n).2 hb)
  obtain ⟨p, k, hp, hpA, hpB, hpab⟩ := sep_prime A.r B.r A.m B.m hdisj
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · simp at hpab
  have hpdvd : (p : ℤ) ∣ 4 * K := by
    rw [← hAm]
    exact (dvd_pow_self (p : ℤ) hk.ne').trans hpA
  have hpS : p = 2 ∨ p ∈ P₁ ∪ P₂ := ((isSmoothModulus_four (P₁ ∪ P₂)).mul hsK) p hp hpdvd
  have s12K : ∀ q : ℕ, q.Prime → (q : ℤ) ∣ K → q = 2 ∨ q ∈ P₁ ∨ q ∈ P₂ := fun q hq hd =>
    (hsK q hq hd).imp_right fun h' => (Set.mem_union q P₁ P₂).1 h'
  have s12L : ∀ q : ℕ, q.Prime → (q : ℤ) ∣ L → q = 2 ∨ q ∈ P₁ ∨ q ∈ P₂ := fun q hq hd =>
    (hsL q hq hd).imp_right fun h' => (Set.mem_union q P₁ P₂).1 h'
  have s21K : ∀ q : ℕ, q.Prime → (q : ℤ) ∣ K → q = 2 ∨ q ∈ P₂ ∨ q ∈ P₁ := fun q hq hd =>
    (s12K q hq hd).imp_right Or.symm
  have s21L : ∀ q : ℕ, q.Prime → (q : ℤ) ∣ L → q = 2 ∨ q ∈ P₂ ∨ q ∈ P₁ := fun q hq hd =>
    (s12L q hq hd).imp_right Or.symm
  rcases hpS with h2 | hpU
  · exact swap_mem_of_sep le_sup_left le_sup_right h hK hL hAm hBm s12K s12L hp (Or.inl h2)
      hpA hpB hpab
  · rcases (Set.mem_union p P₁ P₂).1 hpU with h1 | h2
    · exact swap_mem_of_sep le_sup_left le_sup_right h hK hL hAm hBm s12K s12L hp (Or.inr h1)
        hpA hpB hpab
    · exact swap_mem_of_sep le_sup_right le_sup_left h hK hL hAm hBm s21K s21L hp (Or.inr h2)
        hpA hpB hpab

/-- Every class transposition over `P₁ ∪ P₂` lies in `⟨CT_{P₁}, CT_{P₂}⟩`. -/
theorem swap_mem_sup {P₁ P₂ : Set ℕ} {A B : Box} (h : A.Disj B)
    (hA : IsSmoothModulus (P₁ ∪ P₂) A.m) (hB : IsSmoothModulus (P₁ ∪ P₂) B.m) :
    swap A B h ∈ classTranspositionGroupOver P₁ ⊔ classTranspositionGroupOver P₂ := by
  rw [← swap_split h 4 (by norm_num)]
  apply Subgroup.list_prod_mem
  intro x hx
  obtain ⟨j, -, rfl⟩ := List.mem_map.1 hx
  have e4 : ∀ C : Box, (place C (child 4 j)).m = 4 * C.m := fun C => by
    rw [place_m]
    show ((4 : ℕ) : ℤ) * C.m = 4 * C.m
    norm_num
  unfold kidSwap
  exact swap_mem_sup_of_four (disj_place_of h) A.m_pos B.m_pos (e4 A) (e4 B) hA hB

/-- **Kourovka 21.75, answered negatively**: for any two sets `P₁` and `P₂` of odd primes,
`CT_{P₁}(ℤ)` and `CT_{P₂}(ℤ)` generate `CT_{P₁ ∪ P₂}(ℤ)`, so the inclusion is never proper. -/
theorem kourovka_21_75 :
    ∀ P₁ P₂ : Set ℕ, (∀ p ∈ P₁, p.Prime ∧ p ≠ 2) → (∀ p ∈ P₂, p.Prime ∧ p ≠ 2) →
      classTranspositionGroupOver P₁ ⊔ classTranspositionGroupOver P₂ =
        classTranspositionGroupOver (P₁ ∪ P₂) := by
  intro P₁ P₂ _ _
  apply le_antisymm
  · exact sup_le (classTranspositionGroupOver_mono fun _ hx => Or.inl hx)
      (classTranspositionGroupOver_mono fun _ hx => Or.inr hx)
  · show Subgroup.closure {g | IsClassTranspositionOver (P₁ ∪ P₂) g} ≤ _
    rw [Subgroup.closure_le]
    intro g hg
    have hg' : IsClassTranspositionOver (P₁ ∪ P₂) g := hg
    obtain ⟨A, B, h, hA, hB, rfl⟩ := hg'.eq_swap
    exact swap_mem_sup h hA hB

end GroupApproximation.Kourovka2175
