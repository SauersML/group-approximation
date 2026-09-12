import GroupApproximation.GGT.OsinTheorem54SepPivotDichotomy
import GroupApproximation.GGT.OsinTheorem54SepPivotSpliceReversed
import GroupApproximation.GGT.OsinTheorem54SepIndexSumSplit

/-!
# Osin's Lemma 4.9, discharged

> For any `f, g, h ∈ G` the set `S(f,g;D)` decomposes as `S' ⊔ S'' ⊔ F` with
> `S' ⊆ S(f,h;D)`, `S'' ⊆ S(g,h;D)` and `|F| ≤ 2`.  In particular
> `|S(f,g;D)| ≤ |S(f,h;D)| + |S(g,h;D)| + 2`.

The count carried here is the Λ-sum `∑ λ, |S(f,g;D)_λ|`, which is Osin's
`|S(f,g;D)|` --- his separating cosets range over all `λ` at once --- and the
defect is `2` for the whole sum, not `2` for each `λ`.  That is the form Lemma
5.10's induction consumes, and it is why the constant there is `3 = 1 + 2`.

## The order is the index

Osin enumerates `S(f,g;D) = {C₁ ≺ … ≺ Cₙ}` and picks the largest coset his
geodesic `r` from `f` reaches.  Here the order is not built: by Lemma 4.6 a
separating coset is entered by EVERY geodesic from `f` after the same number of
letters, so the index along one fixed geodesic `p` from `f` to `g` names the
coset, and `≺` is `<` on those indices.  What has to be chosen is therefore a
number: `m`, the largest index whose coset `r` also penetrates
(`Nat.findGreatest`), and `m'`, the next index in use after it (`Nat.find`).

Three bounds then finish it.

* Below `m` the pivot splice sends the coset into `S(f,h;D)`, injectively,
  because distinct indices name distinct cosets.
* Above `m'` the reversed splice sends it into `S(g,h;D)`.  The pivot there is
  `m'` itself, and it is penetrated by the geodesic `q` through `h` for the
  reason Osin gives: `m'` exceeds the largest index `r` reaches, so Lemma 4.5
  leaves only the other side.
* Between them lie at most the two indices `m` and `m'`, and an index belongs to
  at most one `λ` --- a letter is a component letter of one index only.  So the
  middle costs `2` in total, and that is the whole of the defect.

Nothing here spends a constant: `hbnd` and `hDc` are passed through to Lemma
4.5 for the dichotomy alone, and both splices are exact.
-/

namespace GroupApproximation
namespace GGT
namespace OsinComponents

open GroupApproximation.WordMetric

universe u w

variable {G : Type u} [Group G] {Λ : Type w}

/-! ## Two selections of an index -/

/-- **The largest index with a property, if any.** -/
theorem exists_greatest_pivot (P : ℕ → Prop) (N : ℕ) :
    ∃ m : ℕ, (m ≠ 0 → P m) ∧ ∀ n : ℕ, n ≤ N → P n → n ≤ m := by
  classical
  refine ⟨Nat.findGreatest P N, fun h0 => Nat.findGreatest_of_ne_zero rfl h0, ?_⟩
  intro n hn hPn
  by_contra hcon
  exact Nat.findGreatest_is_greatest (by omega) hn hPn

/-- **The least index above a given one, when there is one.** -/
theorem exists_least_above (P : ℕ → Prop) (m : ℕ) (hex : ∃ n : ℕ, m < n ∧ P n) :
    ∃ m' : ℕ, m < m' ∧ P m' ∧ ∀ n : ℕ, m < n → P n → m' ≤ n := by
  classical
  refine ⟨Nat.find hex, (Nat.find_spec hex).1, (Nat.find_spec hex).2, ?_⟩
  intro n hmn hPn
  exact Nat.find_min' hex ⟨hmn, hPn⟩

/-! ## An index belongs to one `λ` -/

omit [Group G] in
/-- **A letter is a component letter of one index only.** -/
theorem isCompOf_unique {a : RelLetter G Λ} {lam mu : Λ}
    (h1 : a.IsCompOf lam) (h2 : a.IsCompOf mu) : lam = mu := by
  cases a with
  | base _ => exact False.elim h1
  | comp nu _ =>
      have e1 : nu = lam := h1
      have e2 : nu = mu := h2
      exact e1.symm.trans e2

/-! ## The witness geodesic, carrying the pivot -/

/-- **One geodesic carries both the essential penetration and the pivot.**

Definition 4.3 names a geodesic on which the penetration at `n` is essential;
Lemma 4.8 puts the pivot's component on that same geodesic; and Lemma 4.6 puts
both at the indices they have on `p`.  The splices need exactly this. -/
theorem exists_witness_and_pivot (D : RelGenSet G Λ) (lam mu : Λ) (Dc : ℕ)
    (h48mu : LemmaFourEight D mu Dc) {f g : G} {p : List (RelLetter G Λ)}
    (hp : IsGeodesicWord D f g p) {n t : ℕ} (hcompn : IsComp lam p n (n + 1))
    (hcn : (QuotientGroup.mk (vertex f p n) : G ⧸ D.fam lam)
      ∈ sepSet D lam Dc f g)
    (hcompt : IsComp mu p t (t + 1))
    (hct : (QuotientGroup.mk (vertex f p t) : G ⧸ D.fam mu)
      ∈ sepSet D mu Dc f g) :
    ∃ w : List (RelLetter G Λ), IsGeodesicWord D f g w ∧
      EssentiallyPenetrates D lam Dc f w n (n + 1) ∧ IsComp mu w t (t + 1) ∧
      (QuotientGroup.mk (vertex f w n) : G ⧸ D.fam lam)
        = QuotientGroup.mk (vertex f p n) ∧
      (QuotientGroup.mk (vertex f w t) : G ⧸ D.fam mu)
        = QuotientGroup.mk (vertex f p t) := by
  obtain ⟨w, i, k, hw, hess, hcw⟩ := hcn
  have hk : k = i + 1 := isComp_eq_succ_of_isGeodesicWord D lam hw hess.1
  subst hk
  have hin : i = n :=
    penetratesAt_index_eq D lam
      (c := (QuotientGroup.mk (vertex f p n) : G ⧸ D.fam lam)) (Dc := Dc) hw hp
      ⟨⟨i + 1, hess.1⟩, hcw⟩ ⟨⟨n + 1, hcompn⟩, rfl⟩
  subst hin
  obtain ⟨i', k', hpivw, hcpw⟩ := h48mu.1 f g w hw _ hct
  have hk' : k' = i' + 1 := isComp_eq_succ_of_isGeodesicWord D mu hw hpivw
  subst hk'
  have hit : i' = t :=
    penetratesAt_index_eq D mu
      (c := (QuotientGroup.mk (vertex f p t) : G ⧸ D.fam mu)) (Dc := Dc) hw hp
      ⟨⟨i' + 1, hpivw⟩, hcpw⟩ ⟨⟨t + 1, hcompt⟩, rfl⟩
  subst hit
  exact ⟨w, hw, hess, hpivw, hcw.symm, hcpw.symm⟩

/-! ## Lemma 4.9 -/

/-- **Osin, Lemma 4.9**, in the Λ-sum form, from the isolated-component bound at
`n ≤ 6` and `C * 4 ≤ Dc`. -/
theorem sum_sepCard_le_of_bound [Fintype Λ] (D : RelGenSet G Λ)
    (hsymm : ∀ x ∈ D.base, x⁻¹ ∈ D.base) {C Dc : ℕ}
    (hbnd : ∀ (n : ℕ), n ≤ 6 → ∀ (v : G) (u : List (RelLetter G Λ)),
      IsQuasiGeodesicPolygon D 1 0 n v u →
      ∀ (nu : Λ) (i k : ℕ), IsComp nu u i k → IsIsolated D.fam nu v u i →
        (vertex v u i)⁻¹ * vertex v u k ∈ D.relBall nu (C * n))
    (hDc : C * 4 ≤ Dc) (h48 : ∀ lam : Λ, LemmaFourEight D lam Dc) (f g h : G) :
    (∑ lam : Λ, sepCard D lam Dc f g)
      ≤ (∑ lam : Λ, sepCard D lam Dc f h)
        + (∑ lam : Λ, sepCard D lam Dc g h) + 2 := by
  classical
  obtain ⟨p, hp⟩ := existsGeodesicWord D f g
  obtain ⟨r, hr⟩ := existsGeodesicWord D f h
  obtain ⟨q, hq⟩ := existsGeodesicWord D h g
  have hqrev : IsGeodesicWord D g h (revWord q) := isGeodesicWord_revWord D hsymm hq
  have hcard : ∀ lam : Λ,
      sepCard D lam Dc f g = (sepIndexSet D lam Dc f g p).ncard :=
    fun lam => sepCard_eq_ncard_sepIndexSet D lam Dc (h48 lam) hp
  have hfin : ∀ lam : Λ, (sepIndexSet D lam Dc f g p).Finite :=
    fun lam => sepIndexSet_finite D lam Dc f g p
  -- what an index carries
  have hAcomp : ∀ (lam : Λ) (n : ℕ), n ∈ sepIndexSet D lam Dc f g p →
      IsComp lam p n (n + 1) ∧
      (QuotientGroup.mk (vertex f p n) : G ⧸ D.fam lam) ∈ sepSet D lam Dc f g := by
    rintro lam n ⟨c, hc, ⟨k, hk⟩, hcc⟩
    have hk1 : k = n + 1 := isComp_eq_succ_of_isGeodesicWord D lam hp hk
    subst hk1
    refine ⟨hk, ?_⟩
    rw [← hcc]
    exact hc
  -- distinct indices of the family never meet
  have hdisj : ∀ (lam mu : Λ) (n : ℕ), n ∈ sepIndexSet D lam Dc f g p →
      n ∈ sepIndexSet D mu Dc f g p → lam = mu := by
    intro lam mu n hn hn'
    have h1 := (hAcomp lam n hn).1
    have h2 := (hAcomp mu n hn').1
    have hnp : n < p.length := by
      have hb := h1.2.1
      omega
    exact isCompOf_unique (h1.2.2.1 n (le_refl n) (by omega) hnp)
      (h2.2.2.1 n (le_refl n) (by omega) hnp)
  -- the pivot index `r` reaches
  obtain ⟨m, hmpos, hmmax⟩ := exists_greatest_pivot
    (fun n => ∃ lam : Λ, n ∈ sepIndexSet D lam Dc f g p ∧
      IsComp lam r n (n + 1) ∧
      (QuotientGroup.mk (vertex f p n) : G ⧸ D.fam lam)
        = QuotientGroup.mk (vertex f r n)) p.length
  -- below the pivot: into `S(f,h;D)`
  have hP1 : ∀ (lam : Λ) (n : ℕ), n ∈ sepIndexSet D lam Dc f g p → n < m →
      (QuotientGroup.mk (vertex f p n) : G ⧸ D.fam lam)
        ∈ sepSet D lam Dc f h := by
    intro lam n hn hnm
    obtain ⟨mu, hmmu, hpivr, hcosr⟩ := hmpos (by omega)
    obtain ⟨hcompm, hcm⟩ := hAcomp mu m hmmu
    obtain ⟨hcompn, hcn⟩ := hAcomp lam n hn
    obtain ⟨w, hw, hessw, hpivw, hwn, hwm⟩ :=
      exists_witness_and_pivot D lam mu Dc (h48 mu) hp hcompn hcn hcompm hcm
    have hres := sepSet_of_essentiallyPenetrates_of_lt_pivot D lam mu Dc hw hr
      hnm hessw hpivw hpivr (hwm.trans hcosr)
    rwa [hwn] at hres
  -- the next index in use, and what lies above it
  obtain ⟨m', hP2, hP3⟩ : ∃ m' : ℕ,
      (∀ (lam : Λ) (n : ℕ), n ∈ sepIndexSet D lam Dc f g p → m' < n →
        (QuotientGroup.mk (vertex f p n) : G ⧸ D.fam lam)
          ∈ sepSet D lam Dc g h) ∧
      (∀ (lam : Λ) (n : ℕ), n ∈ sepIndexSet D lam Dc f g p → m ≤ n → n ≤ m' →
        n = m ∨ n = m') := by
    by_cases hex : ∃ n : ℕ, m < n ∧ ∃ lam : Λ, n ∈ sepIndexSet D lam Dc f g p
    · obtain ⟨m', hmlt, ⟨mu, hm'mu⟩, hmin⟩ := exists_least_above
        (fun n => ∃ lam : Λ, n ∈ sepIndexSet D lam Dc f g p) m hex
      obtain ⟨hcompm', hcm'⟩ := hAcomp mu m' hm'mu
      have hm'p : m' + 1 ≤ p.length := hcompm'.2.1
      -- `r` cannot reach `m'`, so Lemma 4.5 leaves the other side
      have hqpen : ∃ j : ℕ, IsComp mu (revWord q) j (j + 1) ∧
          (QuotientGroup.mk (vertex f p m') : G ⧸ D.fam mu)
            = QuotientGroup.mk (vertex g (revWord q) j) := by
        rcases pivot_dichotomy D mu hsymm hbnd hDc hp hr hq hcompm' hcm' with
          hleft | hright
        · exfalso
          have := hmmax m' (by omega) ⟨mu, hm'mu, hleft.1, hleft.2⟩
          omega
        · exact hright
      obtain ⟨j, hpivq, hcosq⟩ := hqpen
      refine ⟨m', ?_, ?_⟩
      · intro lam n hn hm'n
        obtain ⟨hcompn, hcn⟩ := hAcomp lam n hn
        obtain ⟨w, hw, hessw, hpivw, hwn, hwm'⟩ :=
          exists_witness_and_pivot D lam mu Dc (h48 mu) hp hcompn hcn hcompm' hcm'
        have hres := sepSet_of_essentiallyPenetrates_of_pivot_lt D lam mu Dc hsymm
          hw hqrev hm'n hessw hpivw hpivq (hwm'.trans hcosq)
        rwa [hwn] at hres
      · intro lam n hn hmn hnm'
        by_cases hEq : n = m
        · exact Or.inl hEq
        · have hlt : m < n := by omega
          have hge := hmin n hlt ⟨lam, hn⟩
          exact Or.inr (by omega)
    · refine ⟨m, ?_, ?_⟩
      · intro lam n hn hmn
        exact absurd ⟨n, hmn, lam, hn⟩ hex
      · intro lam n hn hmn hnm
        exact Or.inl (by omega)
  -- the three counts
  have hpre : ∀ lam : Λ,
      (sepIndexSet D lam Dc f g p ∩ {n | n < m}).ncard ≤ sepCard D lam Dc f h := by
    intro lam
    have hinj : Set.InjOn
        (fun n : ℕ => (QuotientGroup.mk (vertex f p n) : G ⧸ D.fam lam))
        (sepIndexSet D lam Dc f g p ∩ {n | n < m}) :=
      (injOn_sepIndexSet D lam Dc hp).mono Set.inter_subset_left
    have himg : (fun n : ℕ => (QuotientGroup.mk (vertex f p n) : G ⧸ D.fam lam)) ''
        (sepIndexSet D lam Dc f g p ∩ {n | n < m}) ⊆ sepSet D lam Dc f h := by
      rintro c ⟨n, ⟨hn, hnm⟩, rfl⟩
      exact hP1 lam n hn hnm
    calc (sepIndexSet D lam Dc f g p ∩ {n | n < m}).ncard
        = ((fun n : ℕ => (QuotientGroup.mk (vertex f p n) : G ⧸ D.fam lam)) ''
            (sepIndexSet D lam Dc f g p ∩ {n | n < m})).ncard :=
          hinj.ncard_image.symm
      _ ≤ (sepSet D lam Dc f h).ncard :=
          Set.ncard_le_ncard himg (sepSet_finite (h48 lam) f h hr)
      _ = sepCard D lam Dc f h := rfl
  have htail : ∀ lam : Λ,
      (sepIndexSet D lam Dc f g p ∩ {n | m' < n}).ncard
        ≤ sepCard D lam Dc g h := by
    intro lam
    have hinj : Set.InjOn
        (fun n : ℕ => (QuotientGroup.mk (vertex f p n) : G ⧸ D.fam lam))
        (sepIndexSet D lam Dc f g p ∩ {n | m' < n}) :=
      (injOn_sepIndexSet D lam Dc hp).mono Set.inter_subset_left
    have himg : (fun n : ℕ => (QuotientGroup.mk (vertex f p n) : G ⧸ D.fam lam)) ''
        (sepIndexSet D lam Dc f g p ∩ {n | m' < n}) ⊆ sepSet D lam Dc g h := by
      rintro c ⟨n, ⟨hn, hnm⟩, rfl⟩
      exact hP2 lam n hn hnm
    calc (sepIndexSet D lam Dc f g p ∩ {n | m' < n}).ncard
        = ((fun n : ℕ => (QuotientGroup.mk (vertex f p n) : G ⧸ D.fam lam)) ''
            (sepIndexSet D lam Dc f g p ∩ {n | m' < n})).ncard :=
          hinj.ncard_image.symm
      _ ≤ (sepSet D lam Dc g h).ncard :=
          Set.ncard_le_ncard himg (sepSet_finite (h48 lam) g h hqrev)
      _ = sepCard D lam Dc g h := rfl
  have h1 : (∑ lam : Λ, (sepIndexSet D lam Dc f g p ∩ {n | n < m}).ncard)
      ≤ ∑ lam : Λ, sepCard D lam Dc f h :=
    Finset.sum_le_sum (fun lam _ => hpre lam)
  have h3 : (∑ lam : Λ, (sepIndexSet D lam Dc f g p ∩ {n | m' < n}).ncard)
      ≤ ∑ lam : Λ, sepCard D lam Dc g h :=
    Finset.sum_le_sum (fun lam _ => htail lam)
  have h2 : (∑ lam : Λ,
      (sepIndexSet D lam Dc f g p ∩ {n | m ≤ n ∧ n ≤ m'}).ncard) ≤ 2 :=
    sum_ncard_middle_le_two (fun lam => sepIndexSet D lam Dc f g p) hfin hdisj hP3
  have h0 : (∑ lam : Λ, sepCard D lam Dc f g)
      ≤ (∑ lam : Λ, (sepIndexSet D lam Dc f g p ∩ {n | n < m}).ncard)
        + (∑ lam : Λ, (sepIndexSet D lam Dc f g p ∩ {n | m ≤ n ∧ n ≤ m'}).ncard)
        + ∑ lam : Λ, (sepIndexSet D lam Dc f g p ∩ {n | m' < n}).ncard := by
    have hstep : ∀ lam : Λ, sepCard D lam Dc f g
        ≤ (sepIndexSet D lam Dc f g p ∩ {n | n < m}).ncard
          + (sepIndexSet D lam Dc f g p ∩ {n | m ≤ n ∧ n ≤ m'}).ncard
          + (sepIndexSet D lam Dc f g p ∩ {n | m' < n}).ncard := by
      intro lam
      rw [hcard lam]
      exact ncard_le_split (sepIndexSet D lam Dc f g p) (hfin lam) m m'
    calc (∑ lam : Λ, sepCard D lam Dc f g)
        ≤ ∑ lam : Λ, ((sepIndexSet D lam Dc f g p ∩ {n | n < m}).ncard
            + (sepIndexSet D lam Dc f g p ∩ {n | m ≤ n ∧ n ≤ m'}).ncard
            + (sepIndexSet D lam Dc f g p ∩ {n | m' < n}).ncard) :=
          Finset.sum_le_sum (fun lam _ => hstep lam)
      _ = (∑ lam : Λ, (sepIndexSet D lam Dc f g p ∩ {n | n < m}).ncard)
            + (∑ lam : Λ,
              (sepIndexSet D lam Dc f g p ∩ {n | m ≤ n ∧ n ≤ m'}).ncard)
            + ∑ lam : Λ, (sepIndexSet D lam Dc f g p ∩ {n | m' < n}).ncard := by
          rw [Finset.sum_add_distrib, Finset.sum_add_distrib]
  omega

/-- **Lemma 4.9 in the shape the assembly's `h49` binder asks for.** -/
theorem lemmaFourNine_of_bound [Fintype Λ] (D : RelGenSet G Λ)
    (hsymm : ∀ x ∈ D.base, x⁻¹ ∈ D.base) {C Dc : ℕ}
    (hbnd : ∀ (n : ℕ), n ≤ 6 → ∀ (v : G) (u : List (RelLetter G Λ)),
      IsQuasiGeodesicPolygon D 1 0 n v u →
      ∀ (nu : Λ) (i k : ℕ), IsComp nu u i k → IsIsolated D.fam nu v u i →
        (vertex v u i)⁻¹ * vertex v u k ∈ D.relBall nu (C * n))
    (hDc : C * 4 ≤ Dc) (h48 : ∀ lam : Λ, LemmaFourEight D lam Dc) :
    ∀ f g h : G, (∑ lam : Λ, sepCard D lam Dc f g)
      ≤ (∑ lam : Λ, sepCard D lam Dc f h)
        + (∑ lam : Λ, sepCard D lam Dc g h) + 2 :=
  fun f g h => sum_sepCard_le_of_bound D hsymm hbnd hDc h48 f g h

/-- **The §4.2 family, discharged together.**  From `hsymm` and four-point
hyperbolicity of the relative graph, both of the assembly's geometric binders
hold for every large enough `Dc`. -/
theorem exists_lemmaFourEight_and_lemmaFourNine_of_fourPointHyperbolic
    [Fintype Λ] (D : RelGenSet G Λ) (hsymm : ∀ x ∈ D.base, x⁻¹ ∈ D.base)
    {δ : ℕ} (hδ : Hyperbolic.IsFourPointHyperbolic D.alphabet.carrier δ) :
    ∃ C : ℕ, 0 < C ∧ ∀ Dc : ℕ, C * 4 ≤ Dc →
      (∀ lam : Λ, LemmaFourEight D lam Dc) ∧
      ∀ f g h : G, (∑ lam : Λ, sepCard D lam Dc f g)
        ≤ (∑ lam : Λ, sepCard D lam Dc f h)
          + (∑ lam : Λ, sepCard D lam Dc g h) + 2 := by
  obtain ⟨C, hCpos, hbnd⟩ :=
    sixBound_one_of_fourPointHyperbolic D hsymm hδ 0 le_rfl
  refine ⟨C, hCpos, fun Dc hDc => ?_⟩
  have h48 : ∀ lam : Λ, LemmaFourEight D lam Dc :=
    lemmaFourEight_forall_of_bound D hsymm hbnd hDc
  exact ⟨h48, lemmaFourNine_of_bound D hsymm hbnd hDc h48⟩

end OsinComponents
end GGT
end GroupApproximation
