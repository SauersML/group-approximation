import GroupApproximation.ClassTransposition.Presentation.Children

/-!
# Uniform trees are canonical

Kourovka 17.61 lane (research node `ct-p-z-is-finitely-presented-by-position-shifting`, Fact O
step O1, in `H P`).

`ku`: a split word on one cell whose leaves all have `K` times the cell's modulus is, in `H P`,
the canonical word `D o qs` followed by a swap word, for every list `qs` of primes with product
`K`. Strong induction on `K`. Let `p` be the root prime and `q` the first prime of `qs`.
* `p = q`: apply `children` to the `p` children.
* `p ≠ q` (`ku_cross`): `p` divides the product of the rest of `qs`. By `children` the children
  are canonical for `q :: qs.erase p`, so they all start with a `q`-split. Bring these forward
  (`regroup`), exchange the root prime (`cx_all`), sort the swaps to the end
  (`exists_split_swaps`) and apply `children` to the `q` children.
-/

namespace GroupApproximation.ClassTransposition.Presentation

open GroupApproximation.Kourovka1759 Equiv Box

variable {P : Set ℕ}

theorem splitAt_cells {b : List Box} {o p : ℕ} {E : Box} (hE : b[o]? = some E) :
    ∀ j, o ≤ j → j < o + p → ∀ F, (splitAt b o p)[j]? = some F → F.m = p * E.m := by
  intro j h1 h2 F hF
  obtain ⟨c, rfl⟩ : ∃ c, j = o + c := ⟨j - o, by omega⟩
  rw [splitAt_get_mid (p := p) b o c E hE (by omega)] at hF
  exact kids_m (List.mem_of_getElem? hF)

theorem nil_of_prod_one : ∀ {qs : List ℕ}, (∀ q ∈ qs, 2 ≤ q) → qs.prod = 1 → qs = []
  | [], _, _ => rfl
  | q :: qs, h, hp => by
    have := h q List.mem_cons_self
    rw [List.prod_cons] at hp
    have := Nat.eq_one_of_mul_eq_one_right hp
    omega

theorem mem_of_dvd_prod {p : ℕ} (hp : p.Prime) : ∀ {qs : List ℕ}, (∀ q ∈ qs, q.Prime) →
    p ∣ qs.prod → p ∈ qs := by
  intro qs h hd
  obtain ⟨a, ha, hpa⟩ := (Prime.dvd_prod_iff hp.prime).1 hd
  rwa [(Nat.prime_dvd_prime_iff_eq hp (h a ha)).1 hpa]

theorem valW_split_locS (hpos : ∀ p ∈ P' P, 2 ≤ p) {b : List Box} {o : ℕ} (ho : o < b.length)
    {t : List Move} (ht : LocS o (o + 1) t) (hpt : PrimesIn P t) : ValW P b.length t :=
  valW_of_locB hpos o t b.length (o + 1) (by omega) (locB_of_locS ht) hpt

section KU

variable (hB : BddAbove (P' P)) (hP2 : 2 ∉ P) (hpos : ∀ p ∈ P' P, 2 ≤ p)
  (hprime : ∀ p ∈ P' P, p.Prime)
include hB hP2 hpos hprime

omit hprime in
/-- The case of different root primes. -/
theorem ku_cross {K : ℕ} (IH : ∀ K' < K, KUstmt P K') {p q : ℕ} (hp : p ∈ P' P) (hq : q ∈ P' P)
    (hpq : p ≠ q) (qs : List ℕ) (hqs : ∀ x ∈ qs, x ∈ P' P) (hpm : p ∈ qs) (hK : K = q * qs.prod)
    {b : List Box} {o : ℕ} {E : Box} (hb : IsPart b) (ho : o < b.length) (hE : b[o]? = some E)
    {S : List Move} (hS : LocS o (o + p) S) (hpS : PrimesIn P S)
    (hU : Unif (real (splitAt b o p) S) o (o + p + growth S) ((K : ℤ) * E.m)) :
    growth S + p = K ∧ ∃ ρ : List ℕ, (∀ k ∈ ρ, o ≤ k ∧ k + 1 < o + p + growth S) ∧
      Eqv P b.length (.split o p :: S) (D o (q :: qs) ++ swaps 0 ρ) := by
  have hp1 := hpos p hp
  have hq1 := hpos q hq
  have hqs1 : ∀ x ∈ qs, 1 ≤ x := fun x hx => by have := hpos x (hqs x hx); omega
  obtain ⟨r, hrP, hprod⟩ : ∃ r : List ℕ, (∀ y ∈ r, y ∈ P' P) ∧ p * r.prod = qs.prod :=
    ⟨qs.erase p, fun y hy => hqs y (List.mem_of_mem_erase hy), List.prod_erase hpm⟩
  have hr1 : ∀ y ∈ r, 1 ≤ y := fun y hy => by have := hpos y (hrP y hy); omega
  have hxpos : 0 < r.prod := List.prod_pos fun a ha => by have := hr1 a ha; omega
  have hqpos : 0 < qs.prod := List.prod_pos fun a ha => by have := hqs1 a ha; omega
  have hK1 : K = p * (q * r.prod) := by rw [hK, ← hprod]; ring
  have hlt1 : q * r.prod < K := by
    rw [hK1]; have : 0 < q * r.prod := Nat.mul_pos (by omega) hxpos
    nlinarith
  have hlt2 : qs.prod < K := by rw [hK]; nlinarith
  -- the `p` children, canonical for `q :: r`
  have hb' := isPart_splitAt hb o (show 0 < p by omega)
  have hlb' : (splitAt b o p).length = b.length + p - 1 := length_splitAt b o p ho
  have hKm : (K : ℤ) * E.m = ((q * r.prod : ℕ) : ℤ) * ((p : ℤ) * E.m) := by rw [hK1]; push_cast; ring
  obtain ⟨hgS, ρ1, hρ1, e1⟩ := children hB hP2 hpos (IH (q * r.prod) hlt1) (q :: r)
    (fun y hy => by rcases List.mem_cons.1 hy with rfl | hy; exacts [hq, hrP y hy])
    (by rw [List.prod_cons]) ((p : ℤ) * E.m) p (splitAt b o p) o S hb' (by omega) hS hpS
    (splitAt_cells hE) (by rw [← hKm]; exact hU)
  have e2 := regroup hB hP2 hpos hq r hrP o p (splitAt b o p).length (by omega)
  have hlev : (Move.split o p).lev b.length = (splitAt b o p).length := by
    rw [lev_split p ho, hlb']
  have f1 : Eqv P b.length (.split o p :: S) ((.split o p :: layer o p q) ++
      (Ch o (p * q) r ++ swaps 0 ρ1)) := by
    refine (Eqv.cons _ (by rw [hlev]; exact e1.trans (e2.append_right _))).trans (Eqv.of_eq ?_)
    simp only [List.cons_append, List.append_assoc]
  -- exchange the root prime
  have hm1 := mul_sub_one_add (p := p) (q := q) (by omega)
  have hm2 := mul_sub_one_add (p := q) (q := p) (by omega)
  have hpq' : q * p = p * q := mul_comm q p
  have hL1 : levW b.length (.split o q :: layer o q p) = b.length + p * q - 1 := by
    rw [levW_cons, lev_split q ho, levW_layer (q := p) (by omega) q o (b.length + q - 1)
      (by omega)]
    omega
  have e3 : Eqv P b.length (.split o p :: layer o p q)
      (.split o q :: layer o q p ++ swaps o (crtWord p q)) := by
    refine ⟨cx_all hB hp hq hpq (by omega) (by omega) b.length o ho, ?_⟩
    rw [levW_append, levW_swaps, hL1, levW_cons, lev_split p ho,
      levW_layer (q := q) (by omega) p o (b.length + p - 1) (by omega)]
    omega
  -- sort the swaps to the end
  have hqr := growth_D r hr1
  have hChg := growth_Ch_of hqr o (p * q)
  have hChl := locS_Ch_of hqr (locS_D r hr1) o (p * q)
  have hW : LocB o (o + p * q) (swaps o (crtWord p q) ++ Ch o (p * q) r) :=
    (locB_append o _ _ _).2 ⟨locB_swaps_at o (p * q) _ (crtWord_lt p q),
      by rw [growth_swaps_at, add_zero]; exact locB_of_locS hChl⟩
  have hpW : PrimesIn P (swaps o (crtWord p q) ++ Ch o (p * q) r) :=
    (primesIn_append _ _).2 ⟨primesIn_swaps_at o _, primesIn_Ch r hrP o (p * q)⟩
  have hgW : growth (swaps o (crtWord p q) ++ Ch o (p * q) r) = growth (Ch o (p * q) r) := by
    rw [growth_append, growth_swaps_at, zero_add]
  obtain ⟨t3, σ2, ht3, hpt3, hg3, hσ2, e4⟩ := exists_split_swaps hB hP2 hpos o _ (b.length + p * q - 1)
    (o + p * q) (by omega) hW hpW
  have e4' : Eqv P (b.length + p * q - 1) (swaps o (crtWord p q) ++ Ch o (p * q) r) (t3 ++ swaps 0 σ2) :=
    eqv_of_toH hpos o (by omega) hW ((locB_append o _ _ _).2 ⟨locB_of_locS ht3,
      locB_swaps σ2 fun k hk => by have := hσ2 k hk; rw [hg3]; exact this⟩) hpW
      ((primesIn_append _ _).2 ⟨hpt3, primesIn_swaps σ2⟩)
      (by rw [growth_append t3, growth_swaps, add_zero, hg3]) e4
  -- the word is now `split o q :: S4 ++ swaps`
  obtain ⟨S4, hS4⟩ : ∃ S4, S4 = layer o q p ++ t3 := ⟨_, rfl⟩
  have hgS4 : growth S4 = q * (p - 1) + growth t3 := by rw [hS4, growth_append, growth_layer]
  have hS4l : LocS o (o + q) S4 := by
    rw [hS4]
    refine (locS_append o _ _ _).2 ⟨locS_layer (by omega) q o, ?_⟩
    rw [growth_layer, show o + q + q * (p - 1) = o + p * q by omega]; exact ht3
  have hpS4 : PrimesIn P S4 := by
    rw [hS4]; exact (primesIn_append _ _).2 ⟨primesIn_layer hp q o, hpt3⟩
  have hA : p * (q * r.prod) = p * q * r.prod := by ring
  have hbd : o + p + growth S = o + q + growth S4 := by rw [hgS4, hg3, hgW]; omega
  have f2 : Eqv P b.length (.split o p :: S) (.split o q :: S4 ++ swaps 0 (σ2 ++ ρ1)) := by
    refine f1.trans ((e3.append_right _).trans ((Eqv.of_eq ?_).trans
      ((Eqv.append_left (.split o q :: layer o q p) (by rw [hL1]; exact e4'.append_right
        (swaps 0 ρ1))).trans (Eqv.of_eq ?_))))
    · simp only [List.append_assoc, List.cons_append]
    · rw [hS4]; simp only [swaps_append, List.cons_append, List.append_assoc]
  have hσ : ∀ k ∈ σ2 ++ ρ1, o ≤ k ∧ k + 1 < o + p + growth S := by
    intro k hk
    rcases List.mem_append.1 hk with hk | hk
    · have := hσ2 k hk; rw [hgW] at this; exact ⟨this.1, by omega⟩
    · exact hρ1 k hk
  -- the `q` children
  have hvT : ValW P b.length (.split o q :: S4 ++ swaps 0 (σ2 ++ ρ1)) := by
    refine valW_of_locB hpos o _ b.length (o + 1) (by omega) ((locB_append o _ _ _).2
      ⟨locB_of_locS ⟨le_rfl, by omega, by rwa [show o + 1 + (q - 1) = o + q by omega]⟩,
       locB_swaps _ fun k hk => ?_⟩) ((primesIn_append _ _).2 ⟨⟨hq, hpS4⟩, primesIn_swaps _⟩)
    have := hσ k hk
    refine ⟨this.1, ?_⟩
    simp only [growth]
    omega
  have hrT := f2.real_eq hpos hP2 (by omega) (valW_split_locS hpos ho
    ⟨le_rfl, by omega, by rwa [show o + 1 + (p - 1) = o + p by omega]⟩ ⟨hp, hpS⟩) hvT hb rfl
  rw [real_append] at hrT
  have hrT' : real (splitAt b o p) S = real (real (splitAt b o q) S4) (swaps 0 (σ2 ++ ρ1)) := hrT
  have hb'' := isPart_splitAt hb o (show 0 < q by omega)
  have hlb'' : (splitAt b o q).length = b.length + q - 1 := length_splitAt b o q ho
  have hlr : o + p + growth S ≤ (real (splitAt b o q) S4).length := by
    rw [length_real, levW_locB hpos o S4 (splitAt b o q).length (o + q) (by omega)
      (locB_of_locS hS4l) hpS4]
    omega
  have hU4 : Unif (real (splitAt b o q) S4) o (o + q + growth S4)
      ((qs.prod : ℕ) * ((q : ℤ) * E.m)) := by
    have h := unif_of_real_swaps (σ2 ++ ρ1) _ hσ hlr (by rw [← hrT']; exact hU)
    rw [← hbd, show ((qs.prod : ℕ) : ℤ) * ((q : ℤ) * E.m) = (K : ℤ) * E.m by
      rw [hK]; push_cast; ring]
    exact h
  obtain ⟨hg4, ρ4, hρ4, e5⟩ := children hB hP2 hpos (IH qs.prod hlt2) qs hqs rfl ((q : ℤ) * E.m) q
    (splitAt b o q) o S4 hb'' (by omega) hS4l hpS4 (splitAt_cells hE) hU4
  have hlq : (Move.split o q).lev b.length = (splitAt b o q).length := by
    rw [lev_split q ho, hlb'']
  refine ⟨by omega, ρ4 ++ (σ2 ++ ρ1), ?_, ?_⟩
  · intro k hk
    rcases List.mem_append.1 hk with hk | hk
    · have := hρ4 k hk; exact ⟨this.1, by omega⟩
    · exact hσ k hk
  · refine f2.trans (((Eqv.cons (.split o q) (by rw [hlq]; exact e5)).append_right _).trans
      (Eqv.of_eq ?_))
    simp only [D_cons, swaps_append, List.cons_append, List.append_assoc]

/-- **Uniform trees are canonical.** -/
theorem ku : ∀ K, KUstmt P K := by
  intro K
  induction K using Nat.strong_induction_on with
  | _ K IH =>
  intro qs hqs hqK b o t hb ho ht hpt hU
  obtain ⟨E, hE⟩ : ∃ E, b[o]? = some E := ⟨b[o], List.getElem?_eq_getElem ho⟩
  have hUE := hU E hE
  have hqs2 : ∀ q ∈ qs, 2 ≤ q := fun q hq => hpos q (hqs q hq)
  rcases t with _ | ⟨m, S⟩
  · -- no split: `K = 1`
    have h1 : E.m = (K : ℤ) * E.m := hUE o le_rfl (by show o < o + 1 + 0; omega) E hE
    have hK1 : (K : ℤ) = 1 := by
      have := mul_right_cancel₀ E.m_ne (h1.symm.trans (one_mul E.m).symm)
      exact this
    have hK : K = 1 := by exact_mod_cast hK1
    have hqs0 := nil_of_prod_one hqs2 (hqK.trans hK)
    subst hqs0
    refine ⟨by show 0 + 1 = K; omega, [], by simp, Eqv.of_eq ?_⟩
    simp [D_nil, swaps]
  cases m with
  | swap k => exact (show False from ht).elim
  | split i p =>
  obtain ⟨hi1, hi2, hS⟩ := ht
  have hio : i = o := by omega
  rw [hio] at hUE ⊢
  obtain ⟨hp, hpS⟩ := hpt
  have hp1 := hpos p hp
  rw [show o + 1 + (p - 1) = o + p by omega] at hS
  have hU' : Unif (real (splitAt b o p) S) o (o + p + growth S) ((K : ℤ) * E.m) :=
    fun j h1 h2 F hF => hUE j h1 (by show j < o + 1 + (p - 1 + growth S); omega) F hF
  have hb' := isPart_splitAt hb o (show 0 < p by omega)
  have hlb' : (splitAt b o p).length = b.length + p - 1 := length_splitAt b o p ho
  have hlev : (Move.split o p).lev b.length = (splitAt b o p).length := by
    rw [lev_split p ho, hlb']
  -- `p` divides `K`
  have hlen : o < (real (splitAt b o p) S).length := by
    rw [length_real, levW_locB hpos o S (splitAt b o p).length (o + p) (by omega)
      (locB_of_locS hS) hpS]
    omega
  obtain ⟨F0, hF0⟩ : ∃ F0, (real (splitAt b o p) S)[o]? = some F0 :=
    ⟨_, List.getElem?_eq_getElem hlen⟩
  have hd := real_dvd hpos (d := (p : ℤ) * E.m) S (splitAt b o p) (o + p) hS hpS (by omega)
    (fun j h1 h2 F hF => Dvd.intro 1 (by rw [splitAt_cells hE j h1 h2 F hF, mul_one]))
    o le_rfl (by omega) F0 hF0
  have hF0m : F0.m = (K : ℤ) * E.m := hU' o le_rfl (by omega) F0 hF0
  rw [hF0m] at hd
  have hpK : p ∣ K := Int.natCast_dvd_natCast.1 ((mul_dvd_mul_iff_right E.m_ne).1 hd)
  have hKpos : 0 < K := by
    rcases Nat.eq_zero_or_pos K with h | h
    · rw [h] at hF0m; have := F0.m_pos; simp at hF0m; omega
    · exact h
  obtain ⟨K1, hK1⟩ := hpK
  have hK1pos : 0 < K1 := Nat.pos_of_ne_zero fun h => by rw [h, mul_zero] at hK1; omega
  have hK1lt : K1 < K := by rw [hK1]; nlinarith
  rcases qs with _ | ⟨q, qs'⟩
  · have h1 : p * K1 = 1 := by rw [← hK1, ← hqK, List.prod_nil]
    have := Nat.eq_one_of_mul_eq_one_right h1
    omega
  have hq : q ∈ P' P := hqs q List.mem_cons_self
  have hqs' : ∀ x ∈ qs', x ∈ P' P := fun x hx => hqs x (List.mem_cons_of_mem _ hx)
  rw [List.prod_cons] at hqK
  by_cases hpq : p = q
  · -- same root prime
    have hK1' : K1 = qs'.prod :=
      Nat.eq_of_mul_eq_mul_left (show 0 < p by omega) (by rw [← hK1, ← hqK, hpq])
    have hKm : (K : ℤ) * E.m = (K1 : ℤ) * ((p : ℤ) * E.m) := by rw [hK1]; push_cast; ring
    obtain ⟨hg, ρ, hρ, e⟩ := children hB hP2 hpos (IH K1 hK1lt) qs' hqs' hK1'.symm
      ((p : ℤ) * E.m) p (splitAt b o p) o S hb' (by omega) hS hpS (splitAt_cells hE)
      (by rw [← hKm]; exact hU')
    refine ⟨by show p - 1 + growth S + 1 = K; rw [hK1]; omega, ρ, fun k hk => by
      have := hρ k hk; show o ≤ k ∧ k + 1 < o + 1 + (p - 1 + growth S); omega, ?_⟩
    rw [D_cons, ← hpq, List.cons_append]
    exact Eqv.cons _ (by rw [hlev]; exact e)
  · -- different root primes
    have hpd : p ∣ qs'.prod := by
      have h2 : p ∣ q * qs'.prod := ⟨K1, by rw [hqK, hK1]⟩
      rcases (Nat.Prime.dvd_mul (hprime p hp)).1 h2 with h | h
      · exact absurd ((Nat.prime_dvd_prime_iff_eq (hprime p hp) (hprime q hq)).1 h) hpq
      · exact h
    have hpm := mem_of_dvd_prod (hprime p hp) (fun y hy => hprime y (hqs' y hy)) hpd
    obtain ⟨hg, ρ, hρ, e⟩ := ku_cross hB hP2 hpos IH hp hq hpq qs' hqs' hpm hqK.symm hb ho hE
      hS hpS hU'
    refine ⟨by show p - 1 + growth S + 1 = K; omega, ρ, fun k hk => by
      have := hρ k hk; show o ≤ k ∧ k + 1 < o + 1 + (p - 1 + growth S); omega, e⟩

end KU

end GroupApproximation.ClassTransposition.Presentation
