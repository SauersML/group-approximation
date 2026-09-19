import GroupApproximation.ClassTransposition.Presentation.RangeY

/-!
# `CT_P(ℤ)` lies in the image of `evalH`

Kourovka 17.61 lane (research node `ct-p-z-is-finitely-presented-by-position-shifting`, §1).

* Two boxes of a realization from `[ℤ]` are exchanged by an element of the image: append the
  swap word that exchanges them (`swap_mem_range_of_mem`).
* For disjoint admissible boxes `A, B`, split both by `k = m_A m_B`. Refine `ℤ` to all classes mod
  `k`, then refine the classes inside `A` by `m_A` and those inside `B` by `m_B`
  (`refine_gen`). The children `A_j, B_j` are boxes of the result, and `t(A,B) = ∏ t(A_j, B_j)`.
-/

namespace GroupApproximation.ClassTransposition.Presentation

open GroupApproximation.Kourovka1759 Equiv Box

variable {P : Set ℕ}

theorem isPN_of_smooth {m : ℤ} (hm : 0 < m) (h : IsSmoothModulus P m) : IsPN P m := by
  refine ⟨m.toNat.primeFactorsList, fun q hq => ?_, ?_⟩
  · have hq' := Nat.prime_of_mem_primeFactorsList hq
    have hd : (q : ℤ) ∣ m := by
      have := Int.natCast_dvd_natCast.2 (Nat.dvd_of_mem_primeFactorsList hq)
      rwa [Int.toNat_of_nonneg hm.le] at this
    exact h q hq' hd
  · rw [Nat.prod_primeFactorsList (by omega), Int.toNat_of_nonneg hm.le]

theorem sub_or_disj {A F : Box} (hd : A.m ∣ F.m) : (∀ n, F.Mem n → A.Mem n) ∨ F.Disj A := by
  by_cases h : A.Mem F.r
  · left
    intro n hn
    have e : n % A.m = n % F.m % A.m := (Int.emod_emod_of_dvd n hd).symm
    show n % A.m = A.r
    rw [e, hn]
    exact h
  · right
    intro n hn ha
    apply h
    show F.r % A.m = A.r
    rw [← hn, Int.emod_emod_of_dvd n hd]
    exact ha

theorem mem_self_r (X : Box) : X.Mem X.r := Int.emod_eq_of_lt X.hr X.hrm

/-- A box whose first point lies only in boxes of its own modulus belongs to the partition. -/
theorem mem_of_cover {R : List Box} (hR : IsPart R) {X : Box}
    (h : ∀ G ∈ R, G.Mem X.r → G.m = X.m) : X ∈ R := by
  obtain ⟨G, hG, hmem⟩ := hR.2 X.r
  have e1 := h G hG hmem
  have e2 : G.r = X.r := by
    have h' : X.r % G.m = G.r := hmem
    rw [e1, Int.emod_eq_of_lt X.hr X.hrm] at h'
    exact h'.symm
  rwa [← Box.ext e2 e1]

/-- **Refinement to a target modulus per box.** -/
theorem refine_gen (T : Box → ℤ) (Q : Box → Prop)
    (hQ : ∀ F q X, Q F → X ∈ kids F q → Q X ∧ T X = T F) (n : ℕ) :
    ∀ b : List Box, (∀ F ∈ b, Q F ∧ RefTo P (T F) n F) →
      ∃ c : List Move, ValW P b.length c ∧ ∀ G ∈ real b c, Q G ∧ G.m = T G := by
  induction n with
  | zero =>
    intro b h
    refine ⟨[], trivial, fun G hG => ⟨(h G hG).1, ?_⟩⟩
    obtain ⟨l, -, hl, hM⟩ := (h G hG).2
    rw [List.length_eq_zero_iff.1 (show l.length = 0 by omega)] at hM
    simpa using hM.symm
  | succ n ih =>
    intro b
    induction b with
    | nil => intro _; exact ⟨[], trivial, fun G hG => absurd hG List.not_mem_nil⟩
    | cons F b ihb =>
      intro h
      obtain ⟨c, hc, hcM⟩ := ihb fun G hG => h G (List.mem_cons_of_mem _ hG)
      obtain ⟨hQF, l, hlP, hln, hM⟩ := h F List.mem_cons_self
      rcases l with _ | ⟨q, l⟩
      · refine ⟨c.map Move.up, valW_map_up c _ hc, fun G hG => ?_⟩
        rw [real_map_up] at hG
        rcases List.mem_cons.1 hG with rfl | hG
        · exact ⟨hQF, by simpa using hM.symm⟩
        · exact hcM G hG
      · have hq := hlP q List.mem_cons_self
        obtain ⟨c', hc', hc'M⟩ := ih (kids F q ++ real b c) fun G hG => by
          rcases List.mem_append.1 hG with hG | hG
          · obtain ⟨hQG, hTG⟩ := hQ F q G hQF hG
            refine ⟨hQG, l, fun x hx => hlP x (List.mem_cons_of_mem _ hx), by simpa using hln, ?_⟩
            rw [hTG, kids_m hG, hM, List.prod_cons, Nat.cast_mul]
            ring
          · exact ⟨(hcM G hG).1, [], by simp, Nat.zero_le _, by rw [(hcM G hG).2]; simp⟩
        refine ⟨c.map Move.up ++ .split 0 q :: c', ?_, fun G hG => hc'M G ?_⟩
        · refine (valW_append P _ _ _).2 ⟨valW_map_up c _ hc, ?_⟩
          rw [List.length_cons, levW_up]
          refine ⟨⟨by omega, hq⟩, ?_⟩
          have e : (kids F q ++ real b c).length = levW b.length c + 1 + q - 1 := by
            rw [List.length_append, length_kids, length_real]; omega
          rw [lev_split (i := 0) (n := levW b.length c + 1) q (by omega), ← e]
          exact hc'
        · rw [real_append, real_map_up] at hG
          exact hG

/-! ### Exchanging two boxes of a realization -/

section Swap

variable (hpos : ∀ p ∈ P' P, 2 ≤ p) (hP2 : 2 ∉ P)
include hpos hP2

theorem swap_mem_range_aux {w : List Move} (hw : ValW P 1 w) {s t1 t2 : List Box} {X Y : Box}
    (hR : real (comb 1) w = s ++ X :: (t1 ++ Y :: t2)) (hXY : X.Disj Y) :
    swap X Y hXY ∈ (evalH hpos hP2).range := by
  have hRp := isPart_real (isPart_comb 1 one_pos) w (ValW.ok hpos hw)
  rw [hR] at hRp
  have hp := hRp.1
  rw [List.pairwise_append] at hp
  obtain ⟨-, hp2, hs⟩ := hp
  rw [List.pairwise_cons] at hp2
  obtain ⟨hX, hp3⟩ := hp2
  rw [List.pairwise_append] at hp3
  obtain ⟨-, hp4, ht1⟩ := hp3
  rw [List.pairwise_cons] at hp4
  obtain ⟨hY, -⟩ := hp4
  have hperm : (s ++ X :: (t1 ++ Y :: t2)).Perm (s ++ Y :: (t1 ++ X :: t2)) := by
    refine List.Perm.append_left s ?_
    exact (List.perm_middle.cons X).trans ((List.Perm.swap Y X _).trans (List.perm_middle.symm.cons Y))
  obtain ⟨σ, hσ, hsw⟩ := exists_swapList _ _ (nodup_of_disj hRp.1) hperm
  have hL : levW 1 w = (s ++ X :: (t1 ++ Y :: t2)).length := by rw [← hR, length_real, length_comb]
  have hw' : ValW P 1 (w ++ swaps 0 σ) :=
    (valW_append P 1 _ _).2 ⟨hw, valW_swaps 0 _ σ fun k hk => by have := hσ k hk; omega⟩
  have hR' : IsPart (s ++ Y :: (t1 ++ X :: t2)) := by
    have := isPart_real (isPart_comb 1 one_pos) _ (ValW.ok hpos hw')
    rwa [real_append, real_swaps_zero, hR, hsw] at this
  have hc : IsPart (comb (levW 1 w)) := isPart_comb _ (by rw [hL]; simp)
  have hcan : List.Forall₂ (CanonOn (swap X Y hXY)) (s ++ X :: (t1 ++ Y :: t2))
      (s ++ Y :: (t1 ++ X :: t2)) := by
    refine forall₂_append' ?_ (.cons (swap_canon hXY) (forall₂_append' ?_
      (.cons (swap_canon' hXY) ?_)))
    · exact List.forall₂_same.2 fun G hG => swap_canon_of_disj hXY (hs G hG X List.mem_cons_self)
        (hs G hG Y (by simp))
    · exact List.forall₂_same.2 fun G hG => swap_canon_of_disj hXY
        (hX G (List.mem_append_left _ hG)).symm (ht1 G hG Y List.mem_cons_self)
    · exact List.forall₂_same.2 fun G hG => swap_canon_of_disj hXY
        (hX G (List.mem_append_right _ (List.mem_cons_of_mem _ hG))).symm (hY G hG).symm
  refine MonoidHom.mem_range.2 ⟨toH P 1 (w ++ swaps 0 σ) * (toH P 1 w)⁻¹, ?_⟩
  rw [map_mul, map_inv, evalH_toH hpos hP2 one_pos hw', evalH_toH hpos hP2 one_pos hw,
    real_append, real_swaps_zero, hR, hsw, levW_append, levW_swaps0,
    frac_inv hc hRp (by rw [length_comb, hL]),
    frac_mul hRp hc hR' (by rw [length_comb, hL]) (by rw [length_comb, hL]; exact hperm.length_eq)]
  exact (eq_frac hRp hR' hcan).symm

/-- Two disjoint boxes of a realization from `[ℤ]` are exchanged by an element of the image. -/
theorem swap_mem_range_of_mem {w : List Move} (hw : ValW P 1 w) {X Y : Box}
    (hX : X ∈ real (comb 1) w) (hY : Y ∈ real (comb 1) w) (hXY : X.Disj Y) :
    swap X Y hXY ∈ (evalH hpos hP2).range := by
  obtain ⟨s, t, hst⟩ := List.append_of_mem hX
  have hne : Y ≠ X := fun e => hXY X.r (mem_self_r X) (by rw [e]; exact mem_self_r X)
  rw [hst] at hY
  rcases List.mem_append.1 hY with hY | hY
  · obtain ⟨s1, s2, rfl⟩ := List.append_of_mem hY
    rw [swap_comm hXY]
    exact swap_mem_range_aux hpos hP2 hw (by rw [hst, List.append_assoc, List.cons_append])
      hXY.symm
  · rcases List.mem_cons.1 hY with h | hY
    · exact absurd h hne
    · obtain ⟨t1, t2, rfl⟩ := List.append_of_mem hY
      exact swap_mem_range_aux hpos hP2 hw hst hXY

end Swap

end GroupApproximation.ClassTransposition.Presentation
