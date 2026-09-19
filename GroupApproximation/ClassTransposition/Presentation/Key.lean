import GroupApproximation.ClassTransposition.Presentation.Refine

/-!
# Equal realizations give equal elements

Kourovka 17.61 lane (research node `ct-p-z-is-finitely-presented-by-position-shifting`, Fact O
steps O1–O2, in `H P`).

* `canon_of_unif`: a valid word from `[ℤ]` whose realization has constant modulus `qs.prod` is
  the canonical word `D 0 qs` followed by a swap word (`exists_split_swaps`, then `ku`).
* `key`: two valid words from `[ℤ]` with the same realization are equal in `H P`. Append the
  same refinement to modulus `M` (`refine_to`), make both canonical, and compare the swap words
  (`perm_eq_of_swapList_eq`, `toH_swaps_eq_of_perm`).
* `ore`: any two valid words from `[ℤ]` have extensions with the same realization.
-/

namespace GroupApproximation.ClassTransposition.Presentation

open GroupApproximation.Kourovka1759 Equiv Box

variable {P : Set ℕ}

theorem isPN_mprod {l : List Box} (h : ∀ F ∈ l, IsPN P F.m) : IsPN P (l.map (·.m)).prod :=
  isPN_prod _ fun x hx => by
    obtain ⟨G, hG, rfl⟩ := List.mem_map.1 hx
    exact h G hG

theorem valW_D_swaps (hpos : ∀ p ∈ P' P, 2 ≤ p) {qs : List ℕ} (hqs : ∀ q ∈ qs, q ∈ P' P)
    {τ : List ℕ} (hτ : ∀ k ∈ τ, k + 1 < qs.prod) : ValW P 1 (D 0 qs ++ swaps 0 τ) := by
  have hqs1 : ∀ q ∈ qs, 1 ≤ q := fun q hq => by have := hpos q (hqs q hq); omega
  have hg := growth_D qs hqs1 0
  exact valW_of_locB hpos 0 _ 1 1 le_rfl ((locB_append 0 1 _ _).2 ⟨locB_of_locS (locS_D qs hqs1 0),
    locB_swaps τ fun k hk => ⟨Nat.zero_le _, by have := hτ k hk; omega⟩⟩)
    ((primesIn_append _ _).2 ⟨primesIn_D qs hqs 0, primesIn_swaps τ⟩)

/-- **Ore condition.** Two valid words from `[ℤ]` have extensions with the same realization. -/
theorem ore (hpos : ∀ p ∈ P' P, 2 ≤ p) {w w' : List Move} (hw : ValW P 1 w) (hw' : ValW P 1 w') :
    ∃ c c' : List Move, ValW P (levW 1 w) c ∧ ValW P (levW 1 w') c' ∧
      real (comb 1) (w ++ c) = real (comb 1) (w' ++ c') := by
  have hpn := isPN_real_one hpos hw
  have hpn' := isPN_real_one hpos hw'
  obtain ⟨l0, hl0, he0⟩ := isPN_mprod hpn
  obtain ⟨l1, hl1, he1⟩ := isPN_mprod hpn'
  have hA : ∀ F ∈ real (comb 1) w, ∃ l : List ℕ, (∀ q ∈ l, q ∈ P' P) ∧
      ((real (comb 1) w).map (·.m)).prod * ((real (comb 1) w').map (·.m)).prod =
        F.m * ((l.prod : ℕ) : ℤ) := fun F hF => by
    obtain ⟨l, hl, he⟩ := ratio_prod hpn F hF
    refine ⟨l ++ l1, fun q hq => ?_, by rw [he, he1, List.prod_append, Nat.cast_mul]; ring⟩
    rcases List.mem_append.1 hq with hq | hq
    exacts [hl q hq, hl1 q hq]
  have hA' : ∀ F ∈ real (comb 1) w', ∃ l : List ℕ, (∀ q ∈ l, q ∈ P' P) ∧
      ((real (comb 1) w).map (·.m)).prod * ((real (comb 1) w').map (·.m)).prod =
        F.m * ((l.prod : ℕ) : ℤ) := fun F hF => by
    obtain ⟨l, hl, he⟩ := ratio_prod hpn' F hF
    refine ⟨l0 ++ l, fun q hq => ?_, by rw [he, he0, List.prod_append, Nat.cast_mul]; ring⟩
    rcases List.mem_append.1 hq with hq | hq
    exacts [hl0 q hq, hl q hq]
  obtain ⟨n, hn⟩ := exists_bound _ hA
  obtain ⟨n', hn'⟩ := exists_bound _ hA'
  obtain ⟨c, hc, hcM⟩ := refine_to n _ hn
  obtain ⟨c1, hc1, hc1M⟩ := refine_to n' _ hn'
  have hb := isPart_real (isPart_comb 1 one_pos) w (ValW.ok hpos hw)
  have hb' := isPart_real (isPart_comb 1 one_pos) w' (ValW.ok hpos hw')
  have hbc := isPart_real hb c (ValW.ok hpos hc)
  have hbc' := isPart_real hb' c1 (ValW.ok hpos hc1)
  have hp := perm_of_unif hbc' hbc hc1M hcM
  obtain ⟨σ, hσ, hsw⟩ := exists_swapList _ _ (nodup_of_disj hbc'.1) hp
  have hL : levW 1 w = (real (comb 1) w).length := by rw [length_real, length_comb]
  have hL' : levW 1 w' = (real (comb 1) w').length := by rw [length_real, length_comb]
  have hlc : levW (levW 1 w') c1 = (real (real (comb 1) w') c1).length := by
    rw [length_real, hL']
  refine ⟨c, c1 ++ swaps 0 σ, by rw [hL]; exact hc, (valW_append P _ _ _).2
    ⟨by rw [hL']; exact hc1, valW_swaps 0 _ σ fun k hk => by have := hσ k hk; omega⟩, ?_⟩
  rw [real_append, ← List.append_assoc, real_append, real_append, real_swaps_zero, hsw]

section Key

variable (hB : BddAbove (P' P)) (hP2 : 2 ∉ P) (hpos : ∀ p ∈ P' P, 2 ≤ p)
  (hprime : ∀ p ∈ P' P, p.Prime)
include hB hP2 hpos hprime

/-- A valid word from `[ℤ]` with a realization of constant modulus is canonical. -/
theorem canon_of_unif {w : List Move} (hw : ValW P 1 w) (qs : List ℕ) (hqs : ∀ q ∈ qs, q ∈ P' P)
    (hU : ∀ G ∈ real (comb 1) w, G.m = ((qs.prod : ℕ) : ℤ)) :
    ∃ τ : List ℕ, (∀ k ∈ τ, k + 1 < qs.prod) ∧ Eqv P 1 w (D 0 qs ++ swaps 0 τ) := by
  obtain ⟨hloc, hpw⟩ := locB_of_valW hpos 1 w hw
  obtain ⟨t, σ, ht, hpt, hg, hσ, e⟩ := exists_split_swaps hB hP2 hpos 0 w 1 1 le_rfl hloc hpw
  have hσ' : ∀ k ∈ σ, 0 ≤ k ∧ k + 1 < 1 + growth t := by rw [hg]; exact hσ
  have htσ : LocB 0 1 (t ++ swaps 0 σ) :=
    (locB_append 0 1 _ _).2 ⟨locB_of_locS ht, locB_swaps σ hσ'⟩
  have hptσ : PrimesIn P (t ++ swaps 0 σ) := (primesIn_append _ _).2 ⟨hpt, primesIn_swaps σ⟩
  have e1 : Eqv P 1 w (t ++ swaps 0 σ) := eqv_of_toH hpos 0 le_rfl hloc htσ hpw hptσ
    (by rw [growth_append, growth_swaps, add_zero, hg]) e
  have hr := e1.real_eq hpos hP2 one_pos hw (valW_of_locB hpos 0 _ 1 1 le_rfl htσ hptσ)
    (isPart_comb 1 one_pos) (length_comb 1)
  rw [real_append] at hr
  have hlt : 0 + 1 + growth t ≤ (real (comb 1) t).length := by
    rw [length_real, length_comb, levW_locB hpos 0 t 1 1 le_rfl (locB_of_locS ht) hpt]; omega
  have hUt : Unif (real (comb 1) t) 0 (0 + 1 + growth t) ((qs.prod : ℕ) : ℤ) :=
    unif_of_real_swaps σ _ (fun k hk => by have := hσ' k hk; exact ⟨this.1, by omega⟩) hlt
      (fun j _ _ G hG => hU G (by rw [hr]; exact List.mem_of_getElem? hG))
  obtain ⟨hgt, ρ, hρ, eK⟩ := ku hB hP2 hpos hprime qs.prod qs hqs rfl (comb 1) 0 t
    (isPart_comb 1 one_pos) (by rw [length_comb]; omega) ht hpt (fun F hF => by
      rw [comb_one] at hF
      have hF' : F = univ := by simpa using hF.symm
      rw [hF', show univ.m = 1 from rfl, mul_one]
      exact hUt)
  rw [length_comb] at eK
  refine ⟨ρ ++ σ, fun k hk => ?_, e1.trans ((eK.append_right _).trans (Eqv.of_eq ?_))⟩
  · rcases List.mem_append.1 hk with hk | hk
    · have := hρ k hk; omega
    · have := hσ' k hk; omega
  · rw [swaps_append, List.append_assoc]

/-- **Equal realizations give equal elements.** -/
theorem key {w w' : List Move} (hw : ValW P 1 w) (hw' : ValW P 1 w')
    (h : real (comb 1) w = real (comb 1) w') : toH P 1 w = toH P 1 w' := by
  have hpn := isPN_real_one hpos hw
  obtain ⟨n, hn⟩ := exists_bound (M := ((real (comb 1) w).map (·.m)).prod) _ (ratio_prod hpn)
  obtain ⟨c, hc, hcM⟩ := refine_to n _ hn
  obtain ⟨qs, hqs, hqM⟩ := isPN_mprod hpn
  have hqs1 : ∀ q ∈ qs, 1 ≤ q := fun q hq => by have := hpos q (hqs q hq); omega
  have hL : levW 1 w = (real (comb 1) w).length := by rw [length_real, length_comb]
  have hL' : levW 1 w' = (real (comb 1) w).length := by rw [h, length_real, length_comb]
  have hwc : ValW P 1 (w ++ c) := (valW_append P 1 w c).2 ⟨hw, by rw [hL]; exact hc⟩
  have hw'c : ValW P 1 (w' ++ c) := (valW_append P 1 w' c).2 ⟨hw', by rw [hL']; exact hc⟩
  have hU : ∀ G ∈ real (comb 1) (w ++ c), G.m = ((qs.prod : ℕ) : ℤ) := by
    rw [real_append, ← hqM]; exact hcM
  have hU' : ∀ G ∈ real (comb 1) (w' ++ c), G.m = ((qs.prod : ℕ) : ℤ) := by
    rw [real_append, ← h, ← hqM]; exact hcM
  obtain ⟨τ, hτ, e1⟩ := canon_of_unif hB hP2 hpos hprime hwc qs hqs hU
  obtain ⟨τ', hτ', e2⟩ := canon_of_unif hB hP2 hpos hprime hw'c qs hqs hU'
  have r1 := e1.real_eq hpos hP2 one_pos hwc (valW_D_swaps hpos hqs hτ) (isPart_comb 1 one_pos)
    (length_comb 1)
  have r2 := e2.real_eq hpos hP2 one_pos hw'c (valW_D_swaps hpos hqs hτ') (isPart_comb 1 one_pos)
    (length_comb 1)
  have r : real (comb 1) (D 0 qs ++ swaps 0 τ) = real (comb 1) (D 0 qs ++ swaps 0 τ') := by
    rw [← r1, ← r2, real_append, real_append, h]
  rw [real_append, real_append, real_swaps_zero, real_swaps_zero] at r
  have hd := isPart_real (isPart_comb 1 one_pos) (D 0 qs) (ok_of_primesIn hpos _ (primesIn_D qs hqs 0))
  have hlD : levW 1 (D 0 qs) = qs.prod := by
    rw [levW_locB hpos 0 (D 0 qs) 1 1 le_rfl (locB_of_locS (locS_D qs hqs1 0)) (primesIn_D qs hqs 0)]
    have := growth_D qs hqs1 0
    omega
  have hlen : (real (comb 1) (D 0 qs)).length = qs.prod := by rw [length_real, length_comb, hlD]
  have hperm := perm_eq_of_swapList_eq (nodup_of_disj hd.1) (fun k hk => by rw [hlen]; exact hτ k hk)
    (fun k hk => by rw [hlen]; exact hτ' k hk) r
  have hs : toH P (levW 1 (D 0 qs)) (swaps 0 τ) = toH P (levW 1 (D 0 qs)) (swaps 0 τ') :=
    toH_swaps_eq_of_perm hB hP2 hpos (fun k hk => by rw [hlD]; exact hτ k hk)
      (fun k hk => by rw [hlD]; exact hτ' k hk) hperm
  have e3 : toH P 1 (w ++ c) = toH P 1 (w' ++ c) := by
    rw [e1.1, e2.1, toH_append, toH_append, hs]
  rw [toH_append, toH_append, hL, hL'] at e3
  exact mul_right_cancel e3

end Key

end GroupApproximation.ClassTransposition.Presentation
