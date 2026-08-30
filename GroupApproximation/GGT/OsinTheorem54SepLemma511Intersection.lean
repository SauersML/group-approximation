import GroupApproximation.GGT.OsinTheorem54SepLemma49
import GroupApproximation.GGT.OsinTheorem54SepLemma511Count
import GroupApproximation.GGT.DGOIsolatedComponentSplit

/-!
# Osin's Lemma 5.11: the shared separating coset

This file formalizes equation (37) and the entrance-point enumeration in the
proof of Osin's Lemma 5.11.  Separating cosets are tagged by their family
index, so their cardinality is exactly the `Λ`-sum used throughout the
separating-coset development.

The setwise form of Lemma 4.9 says that `S(f,g;D)` is covered by the two other
sides of the triangle and at most two exceptional cosets.  Applying it to the
two triangles `(1,z,k)` and `(z,k,kz)` shows that every separator of `(1,z)`
which is not shared with `(k,kz)` lies in one of two short sides or one of four
exceptional cosets.  Lemma 5.10 then gives

`|S(1,z;D) \ S(k,kz;D)| ≤ 6m + 4`,

while `d(1,z) = 18m+11` gives `|S(1,z;D)| ≥ 9m+5`.  Hence the intersection has
at least `3m+1` elements, which is equation (37).

The only geometric input left after that count is equation (38): for a shared
coset outside `S(1,k;D)`, its two entrance points differ by an element of a
relative ball of radius `3Dc`.  `Lemma511SharedGap` records exactly that input.
The last theorem chooses a shared coset outside the at most `3m` forbidden
ones, enumerates the at most `3R` entrance points by `Fin (3R)`, and produces
`Lemma511EntranceEncoding`.
-/

namespace GroupApproximation
namespace GGT
namespace OsinComponents

open GroupApproximation.WordMetric

noncomputable section

universe u w

variable {G : Type u} [Group G] {Λ : Type w}

local instance instDecidableEqG : DecidableEq G := Classical.decEq G
local instance instDecidableEqLambda : DecidableEq Λ := Classical.decEq Λ

/-- A separating coset tagged by the member of the peripheral family to which
it belongs.  The tag makes the union over `Λ` disjoint. -/
abbrev TaggedSepCoset (D : RelGenSet G Λ) :=
  Σ lam : Λ, G ⧸ D.fam lam

local instance instDecidableEqTagged (D : RelGenSet G Λ) :
    DecidableEq (TaggedSepCoset D) := Classical.decEq (TaggedSepCoset D)

/-- The finite set of all separating cosets, over the whole family. -/
noncomputable def sepFinset [Fintype Λ] (D : RelGenSet G Λ) (Dc : ℕ)
    (h48 : ∀ lam : Λ, LemmaFourEight D lam Dc) (f g : G) :
    Finset (TaggedSepCoset D) :=
  Finset.univ.sigma fun lam => (sepSet_finite' (h48 lam) f g).toFinset

@[simp]
theorem mem_sepFinset [Fintype Λ] (D : RelGenSet G Λ) (Dc : ℕ)
    (h48 : ∀ lam : Λ, LemmaFourEight D lam Dc) (lam : Λ)
    (c : G ⧸ D.fam lam) (f g : G) :
    Sigma.mk lam c ∈ sepFinset D Dc h48 f g ↔ c ∈ sepSet D lam Dc f g := by
  classical
  simp [sepFinset]

/-- The tagged finite set has cardinality equal to Osin's `Λ`-sum. -/
theorem card_sepFinset [Fintype Λ] (D : RelGenSet G Λ) (Dc : ℕ)
    (h48 : ∀ lam : Λ, LemmaFourEight D lam Dc) (f g : G) :
    (sepFinset D Dc h48 f g).card = ∑ lam : Λ, sepCard D lam Dc f g := by
  classical
  rw [sepFinset, Finset.card_sigma]
  refine Finset.sum_congr rfl fun lam _ => ?_
  simpa [sepCard] using
    (Set.ncard_eq_toFinset_card (sepSet D lam Dc f g)
      (sepSet_finite' (h48 lam) f g)).symm

/-- **Lemma 4.9 in its setwise form.**  The existing numerical consequence is
`sum_sepCard_le_of_bound`; Lemma 5.11 needs the cover itself in order to count
the intersection of two separating sets. -/
def LemmaFourNineCover [Fintype Λ] (D : RelGenSet G Λ) (Dc : ℕ)
    (h48 : ∀ lam : Λ, LemmaFourEight D lam Dc) : Prop :=
  ∀ f g h : G, ∃ F : Finset (TaggedSepCoset D), F.card ≤ 2 ∧
    sepFinset D Dc h48 f g ⊆
      (sepFinset D Dc h48 f h ∪ sepFinset D Dc h48 g h) ∪ F

/-- **The setwise form of Osin's Lemma 4.9, from the polygon bound.**

The two exceptional cosets are the separators entered at the pivot index `m`
and at the next used index `m'`.  An index belongs to at most one peripheral
family, so each contributes at most one tagged coset. -/
theorem lemmaFourNineCover_of_bound [Fintype Λ] (D : RelGenSet G Λ)
    (hsymm : ∀ x ∈ D.base, x⁻¹ ∈ D.base) {C Dc : ℕ}
    (hbnd : ∀ (n : ℕ), n ≤ 6 → ∀ (v : G) (u : List (RelLetter G Λ)),
      IsQuasiGeodesicPolygon D 1 0 n v u →
      ∀ (nu : Λ) (i k : ℕ), IsComp nu u i k → IsIsolated D.fam nu v u i →
        (vertex v u i)⁻¹ * vertex v u k ∈ D.relBall nu (C * n))
    (hDc : C * 4 ≤ Dc) (h48 : ∀ lam : Λ, LemmaFourEight D lam Dc) :
    LemmaFourNineCover D Dc h48 := by
  classical
  intro f g h
  obtain ⟨p, hp⟩ := existsGeodesicWord D f g
  obtain ⟨r, hr⟩ := existsGeodesicWord D f h
  obtain ⟨q, hq⟩ := existsGeodesicWord D h g
  have hqrev : IsGeodesicWord D g h (revWord q) :=
    isGeodesicWord_revWord D hsymm hq
  have hAcomp : ∀ (lam : Λ) (n : ℕ), n ∈ sepIndexSet D lam Dc f g p →
      IsComp lam p n (n + 1) ∧
      (QuotientGroup.mk (vertex f p n) : G ⧸ D.fam lam) ∈
        sepSet D lam Dc f g := by
    rintro lam n ⟨c, hc, ⟨k, hk⟩, hcc⟩
    have hk1 : k = n + 1 := isComp_eq_succ_of_isGeodesicWord D lam hp hk
    subst hk1
    refine ⟨hk, ?_⟩
    rw [← hcc]
    exact hc
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
  obtain ⟨m, hmpos, hmmax⟩ := exists_greatest_pivot
    (fun n => ∃ lam : Λ, n ∈ sepIndexSet D lam Dc f g p ∧
      IsComp lam r n (n + 1) ∧
      (QuotientGroup.mk (vertex f p n) : G ⧸ D.fam lam)
        = QuotientGroup.mk (vertex f r n)) p.length
  have hP1 : ∀ (lam : Λ) (n : ℕ), n ∈ sepIndexSet D lam Dc f g p → n < m →
      (QuotientGroup.mk (vertex f p n) : G ⧸ D.fam lam) ∈
        sepSet D lam Dc f h := by
    intro lam n hn hnm
    obtain ⟨mu, hmmu, hpivr, hcosr⟩ := hmpos (by omega)
    obtain ⟨hcompm, hcm⟩ := hAcomp mu m hmmu
    obtain ⟨hcompn, hcn⟩ := hAcomp lam n hn
    obtain ⟨w, hw, hessw, hpivw, hwn, hwm⟩ :=
      exists_witness_and_pivot D lam mu Dc (h48 mu) hp hcompn hcn hcompm hcm
    have hres := sepSet_of_essentiallyPenetrates_of_lt_pivot D lam mu Dc hw hr
      hnm hessw hpivw hpivr (hwm.trans hcosr)
    rwa [hwn] at hres
  obtain ⟨m', hP2, hP3⟩ : ∃ m' : ℕ,
      (∀ (lam : Λ) (n : ℕ), n ∈ sepIndexSet D lam Dc f g p → m' < n →
        (QuotientGroup.mk (vertex f p n) : G ⧸ D.fam lam) ∈
          sepSet D lam Dc g h) ∧
      (∀ (lam : Λ) (n : ℕ), n ∈ sepIndexSet D lam Dc f g p →
        m ≤ n → n ≤ m' → n = m ∨ n = m') := by
    by_cases hex : ∃ n : ℕ, m < n ∧ ∃ lam : Λ,
        n ∈ sepIndexSet D lam Dc f g p
    · obtain ⟨m', hmlt, ⟨mu, hm'mu⟩, hmin⟩ := exists_least_above
        (fun n => ∃ lam : Λ, n ∈ sepIndexSet D lam Dc f g p) m hex
      obtain ⟨hcompm', hcm'⟩ := hAcomp mu m' hm'mu
      have hm'p : m' + 1 ≤ p.length := hcompm'.2.1
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
  let exceptionalAt (t : ℕ) : Finset (TaggedSepCoset D) :=
    (Finset.univ.filter fun lam : Λ => t ∈ sepIndexSet D lam Dc f g p).image
      fun lam => Sigma.mk lam
        (QuotientGroup.mk (vertex f p t) : G ⧸ D.fam lam)
  let F := exceptionalAt m ∪ exceptionalAt m'
  have hexceptionalAt : ∀ t : ℕ, (exceptionalAt t).card ≤ 1 := by
    intro t
    apply le_trans Finset.card_image_le
    refine Finset.card_le_one.mpr ?_
    intro lam hlam mu hmu
    exact hdisj lam mu t (Finset.mem_filter.mp hlam).2
      (Finset.mem_filter.mp hmu).2
  have hFcard : F.card ≤ 2 := by
    have hU := Finset.card_union_le (exceptionalAt m) (exceptionalAt m')
    have hmcard := hexceptionalAt m
    have hm'card := hexceptionalAt m'
    change (exceptionalAt m ∪ exceptionalAt m').card ≤ 2
    omega
  refine ⟨F, hFcard, ?_⟩
  rintro ⟨lam, c⟩ hc
  have hcsep : c ∈ sepSet D lam Dc f g :=
    (mem_sepFinset D Dc h48 lam c f g).mp hc
  rw [sepSet_eq_image D lam Dc (h48 lam) hp] at hcsep
  obtain ⟨n, hn, hnc⟩ := hcsep
  by_cases hnm : n < m
  · apply Finset.mem_union.mpr
    apply Or.inl
    apply Finset.mem_union.mpr
    apply Or.inl
    apply (mem_sepFinset D Dc h48 lam c f h).mpr
    rw [← hnc]
    exact hP1 lam n hn hnm
  · by_cases hm'n : m' < n
    · apply Finset.mem_union.mpr
      apply Or.inl
      apply Finset.mem_union.mpr
      apply Or.inr
      apply (mem_sepFinset D Dc h48 lam c g h).mpr
      rw [← hnc]
      exact hP2 lam n hn hm'n
    · have hmid := hP3 lam n hn (by omega) (by omega)
      apply Finset.mem_union.mpr
      apply Or.inr
      rcases hmid with rfl | rfl
      · apply Finset.mem_union.mpr
        apply Or.inl
        change Sigma.mk lam c ∈ exceptionalAt n
        rw [← hnc]
        exact Finset.mem_image.mpr ⟨lam,
          Finset.mem_filter.mpr ⟨Finset.mem_univ _, hn⟩, rfl⟩
      · apply Finset.mem_union.mpr
        apply Or.inr
        change Sigma.mk lam c ∈ exceptionalAt n
        rw [← hnc]
        exact Finset.mem_image.mpr ⟨lam,
          Finset.mem_filter.mpr ⟨Finset.mem_univ _, hn⟩, rfl⟩

/-- **Equation (37) of Osin's Lemma 5.11.** -/
theorem card_sharedSeparators_lower_bound [Fintype Λ]
    (D Y : RelGenSet G Λ) (Dc : ℕ)
    (h48 : ∀ lam : Λ, LemmaFourEight D lam Dc)
    (h49 : LemmaFourNineCover D Dc h48)
    (hdist : ∀ f g : G, wordDist Y.alphabet.carrier f g
      ≤ 2 * (∑ lam : Λ, sepCard D lam Dc f g) + 1)
    (hsle : ∀ f g : G, (∑ lam : Λ, sepCard D lam Dc f g)
      ≤ 3 * wordDist Y.alphabet.carrier f g)
    (m : ℕ) (z k : G) (hz : wordDist Y.alphabet.carrier 1 z = 18 * m + 11)
    (hk : k ∈ ConjDisplacement Y m z) :
    3 * m + 1 ≤
      ((sepFinset D Dc h48 1 z) ∩
        (sepFinset D Dc h48 k (k * z))).card := by
  classical
  let A := sepFinset D Dc h48 1 z
  let B := sepFinset D Dc h48 k (k * z)
  let P := sepFinset D Dc h48 1 k
  let Q := sepFinset D Dc h48 z k
  let T := sepFinset D Dc h48 z (k * z)
  obtain ⟨F₁, hF₁, hcover₁⟩ := h49 1 z k
  obtain ⟨F₂, hF₂, hcover₂⟩ := h49 z k (k * z)
  have hsub : A \ B ⊆ (((P ∪ T) ∪ F₁) ∪ F₂) := by
    intro c hc
    have hcA : c ∈ A := (Finset.mem_sdiff.mp hc).1
    have hcB : c ∉ B := (Finset.mem_sdiff.mp hc).2
    have h₁ := hcover₁ hcA
    rcases Finset.mem_union.mp h₁ with hPQ | hF
    · rcases Finset.mem_union.mp hPQ with hP | hQ
      · exact Finset.mem_union.mpr (Or.inl
          (Finset.mem_union.mpr (Or.inl (Finset.mem_union.mpr (Or.inl hP)))))
      · have h₂ := hcover₂ hQ
        rcases Finset.mem_union.mp h₂ with hTB | hF'
        · rcases Finset.mem_union.mp hTB with hT | hB
          · exact Finset.mem_union.mpr (Or.inl
              (Finset.mem_union.mpr (Or.inl (Finset.mem_union.mpr (Or.inr hT)))))
          · exact False.elim (hcB hB)
        · exact Finset.mem_union.mpr (Or.inr hF')
    · exact Finset.mem_union.mpr (Or.inl (Finset.mem_union.mpr (Or.inr hF)))
  have hPcard : P.card ≤ 3 * m := by
    have h := hsle 1 k
    rw [← card_sepFinset D Dc h48] at h
    exact le_trans h (Nat.mul_le_mul_left 3 hk.1)
  have hdistT : wordDist Y.alphabet.carrier z (k * z)
      = wordDist Y.alphabet.carrier 1 (z⁻¹ * k * z) := by
    have h := (wordDist_left_invariant Y.alphabet.carrier z⁻¹ z (k * z)).symm
    simpa only [inv_mul_cancel, mul_assoc] using h
  have hTcard : T.card ≤ 3 * m := by
    have h := hsle z (k * z)
    rw [← card_sepFinset D Dc h48, hdistT] at h
    exact le_trans h (Nat.mul_le_mul_left 3 hk.2)
  have hdiff : (A \ B).card ≤ 6 * m + 4 := by
    have hcard := Finset.card_le_card hsub
    have hU₁ := Finset.card_union_le P T
    have hU₂ := Finset.card_union_le (P ∪ T) F₁
    have hU₃ := Finset.card_union_le ((P ∪ T) ∪ F₁) F₂
    omega
  have hAcard : 9 * m + 5 ≤ A.card := by
    have h := hdist 1 z
    have hAeq := card_sepFinset D Dc h48 1 z
    change A.card = ∑ lam : Λ, sepCard D lam Dc 1 z at hAeq
    rw [hz, ← hAeq] at h
    omega
  have hsplit := Finset.card_sdiff_add_card_inter A B
  change 3 * m + 1 ≤ (A ∩ B).card
  omega

/-- **The local four-gon estimate in equation (38).**

The two components are the occurrences of one shared coset on a fixed geodesic
from `1` to `z` and on its left translate from `k` to `kz`.  If that coset does
not separate `1` from `k`, the relative distance between their entrance points
is at most `3Dc`.  This is the only polygon-geometric statement left by the
bookkeeping theorem below. -/
def Lemma511EntranceGapBound (D : RelGenSet G Λ) (Dc : ℕ) : Prop :=
  ∀ (lam : Λ) (k z : G) (p : List (RelLetter G Λ))
    (i i' j j' : ℕ), IsGeodesicWord D 1 z p →
      IsComp lam p i i' → IsComp lam p j j' →
      (QuotientGroup.mk (vertex (1 : G) p i) : G ⧸ D.fam lam) =
        QuotientGroup.mk (vertex k p j) →
      (QuotientGroup.mk (vertex (1 : G) p i) : G ⧸ D.fam lam) ∉
        sepSet D lam Dc 1 k →
      (vertex (1 : G) p i)⁻¹ * vertex k p j ∈ D.relBall lam (3 * Dc)

/-- **The two cases in Osin's four-gon proof of equation (38).**

Join the two entrance points by the single `H_lam`-edge `e` and complete the
quadrilateral with a geodesic `s : 1 → k`.  If `e` is isolated, Lemma 4.2 puts
its span directly in the radius-`Dc` relative ball.  Otherwise `e` is connected
to a component `d` of `s`; the two triangular connector estimates put
`u⁻¹d₋` and `d₊⁻¹v` in that ball.  The components on the two translates of `p`
cannot be the match because those sides are geodesic.

This disjunction is exactly the geometric case split in the paper. -/
def Lemma511FourGonAlternative (D : RelGenSet G Λ) (Dc : ℕ) : Prop :=
  ∀ (lam : Λ) (k z : G) (p : List (RelLetter G Λ))
    (i i' j j' : ℕ), IsGeodesicWord D 1 z p →
      IsComp lam p i i' → IsComp lam p j j' →
      (QuotientGroup.mk (vertex (1 : G) p i) : G ⧸ D.fam lam) =
        QuotientGroup.mk (vertex k p j) →
      (QuotientGroup.mk (vertex (1 : G) p i) : G ⧸ D.fam lam) ∉
        sepSet D lam Dc 1 k →
      (vertex (1 : G) p i)⁻¹ * vertex k p j ∈ D.relBall lam Dc ∨
        ∃ (s : List (RelLetter G Λ)) (a a' : ℕ),
          IsGeodesicWord D 1 k s ∧ IsComp lam s a a' ∧
            (vertex (1 : G) p i)⁻¹ * vertex (1 : G) s a ∈ D.relBall lam Dc ∧
            (vertex (1 : G) s a')⁻¹ * vertex k p j ∈ D.relBall lam Dc

/-- **The four-gon alternative implies equation (38).**

In the isolated-edge branch, monotonicity gives the stated radius.  In the
matched-component branch, a middle span outside the radius-`Dc` ball would make
the shared coset a member of `S(1,k;Dc)`; composing the two connectors with the
therefore-short middle span gives radius `3Dc`. -/
theorem entranceGapBound_of_fourGonAlternative (D : RelGenSet G Λ) (Dc : ℕ)
    (halt : Lemma511FourGonAlternative D Dc) :
    Lemma511EntranceGapBound D Dc := by
  intro lam k z p i i' j j' hp hi hj hcos hnot
  rcases halt lam k z p i i' j j' hp hi hj hcos hnot with hdirect |
      ⟨s, a, a', hs, hd, hleft, hright⟩
  · exact relBall_mono_radius D lam (by omega) hdirect
  have hmid :
      (vertex (1 : G) s a)⁻¹ * vertex (1 : G) s a' ∈ D.relBall lam Dc := by
    by_contra hdeep
    apply hnot
    refine ⟨s, a, a', hs, ⟨hd, hdeep⟩, ?_⟩
    exact QuotientGroup.eq.mpr hleft.1
  have hfirst := span_mem_relBall_of_split D lam hleft hmid
  have hall := span_mem_relBall_of_split D lam hfirst hright
  have hrad : Dc + Dc + Dc = 3 * Dc := by omega
  rwa [hrad] at hall

/-- The geometric remainder of Lemma 5.11 after equation (37).

For a fixed geodesic from `1` to `z`, `entrance c` is its entrance point in a
separating coset `c`.  If `c` is also penetrated by the translate from `k` to
`kz` and does not separate `1` from `k`, equation (38) gives the middle factor
in a relative ball of radius `3Dc`; translating the second entrance back gives
another entrance point of the fixed geodesic. -/
def Lemma511SharedGap [Fintype Λ] (D Y : RelGenSet G Λ) (Dc : ℕ)
    (h48 : ∀ lam : Λ, LemmaFourEight D lam Dc) : Prop :=
  ∀ (m : ℕ) (z : G), wordDist Y.alphabet.carrier 1 z = 18 * m + 11 →
    ∃ entrance : TaggedSepCoset D → G,
      ∀ k ∈ ConjDisplacement Y m z, ∀ c : TaggedSepCoset D,
        c ∈ sepFinset D Dc h48 1 z →
        c ∈ sepFinset D Dc h48 k (k * z) →
        c ∉ sepFinset D Dc h48 1 k →
        ∃ c' ∈ sepFinset D Dc h48 1 z, ∃ a : G,
          a ∈ ⋃ lam : Λ, D.relBall lam (3 * Dc) ∧
            k = entrance c * a * (entrance c')⁻¹

/-- **The local estimate (38) supplies the shared-gap interface.**

Fix one geodesic `p : 1 → z`.  Lemma 4.8 gives a unique entrance index on `p`
for every separator.  A shared separator is also penetrated by the translated
geodesic `k·p`; translating that coset back gives another separator of
`(1,z)`, and uniqueness identifies its chosen entrance with the corresponding
vertex of `p`.  The factorization of `k` is then a group identity. -/
theorem sharedGap_of_entranceGapBound [Fintype Λ]
    (D Y : RelGenSet G Λ) (Dc : ℕ)
    (h48 : ∀ lam : Λ, LemmaFourEight D lam Dc)
    (hgap : Lemma511EntranceGapBound D Dc) :
    Lemma511SharedGap D Y Dc h48 := by
  classical
  intro m z hz
  obtain ⟨p, hp⟩ := existsGeodesicWord D 1 z
  let A := sepFinset D Dc h48 1 z
  have hindex : ∀ c : TaggedSepCoset D, ∃ i : ℕ,
      c ∈ A → PenetratesAt D c.1 Dc 1 p i c.2 := by
    intro c
    by_cases hc : c ∈ A
    · have hcsep : c.2 ∈ sepSet D c.1 Dc 1 z :=
        (mem_sepFinset D Dc h48 c.1 c.2 1 z).mp hc
      obtain ⟨i, i', hcomp, hcos⟩ := (h48 c.1).1 1 z p hp c.2 hcsep
      exact ⟨i, fun _ => ⟨⟨i', hcomp⟩, hcos⟩⟩
    · exact ⟨0, fun hc' => False.elim (hc hc')⟩
  let index : TaggedSepCoset D → ℕ := fun c => Classical.choose (hindex c)
  let entrance : TaggedSepCoset D → G := fun c => vertex (1 : G) p (index c)
  have hindex_spec : ∀ (c : TaggedSepCoset D), c ∈ A →
      PenetratesAt D c.1 Dc 1 p (index c) c.2 := by
    intro c hc
    exact Classical.choose_spec (hindex c) hc
  refine ⟨entrance, ?_⟩
  intro k hk c hcA hcB hcP
  have hic := hindex_spec c hcA
  obtain ⟨i', hicomp⟩ := hic.1
  have hpk : IsGeodesicWord D k (k * z) p := by
    have h := (isGeodesicWord_mul_left D k 1 z p).mpr hp
    simpa using h
  have hcBsep : c.2 ∈ sepSet D c.1 Dc k (k * z) :=
    (mem_sepFinset D Dc h48 c.1 c.2 k (k * z)).mp hcB
  obtain ⟨j, j', hjcomp, hjcos⟩ :=
    (h48 c.1).1 k (k * z) p hpk c.2 hcBsep
  have hcos :
      (QuotientGroup.mk (vertex (1 : G) p (index c)) : G ⧸ D.fam c.1) =
        QuotientGroup.mk (vertex k p j) := hic.2.symm.trans hjcos
  have hcPsep : c.2 ∉ sepSet D c.1 Dc 1 k := by
    intro hcsep
    exact hcP ((mem_sepFinset D Dc h48 c.1 c.2 1 k).mpr hcsep)
  have hnot :
      (QuotientGroup.mk (vertex (1 : G) p (index c)) : G ⧸ D.fam c.1) ∉
        sepSet D c.1 Dc 1 k := by
    rwa [← hic.2]
  have hball := hgap c.1 k z p (index c) i' j j' hp hicomp hjcomp hcos hnot
  let c' : TaggedSepCoset D :=
    Sigma.mk c.1 (QuotientGroup.mk (vertex (1 : G) p j) : G ⧸ D.fam c.1)
  have hvertexG : k * vertex (1 : G) p j = vertex k p j := by
    simpa using (vertex_mul_left k 1 p j).symm
  have hc'A : c' ∈ A := by
    have hsmul := sepSet_smul D c.1 Dc k 1 z
    have hsmul' : sepSet D c.1 Dc k (k * z) =
        (fun d : G ⧸ D.fam c.1 => k • d) '' sepSet D c.1 Dc 1 z := by
      simpa using hsmul
    have hcimg : c.2 ∈
        (fun d : G ⧸ D.fam c.1 => k • d) '' sepSet D c.1 Dc 1 z := by
      rw [← hsmul']
      exact hcBsep
    obtain ⟨d, hd, hdc⟩ := hcimg
    have hvertex :
        k • (QuotientGroup.mk (vertex (1 : G) p j) : G ⧸ D.fam c.1) =
          QuotientGroup.mk (vertex k p j) := by
      change QuotientGroup.mk (k * vertex (1 : G) p j) =
        QuotientGroup.mk (vertex k p j)
      rw [hvertexG]
    have hkd : k • d =
        k • (QuotientGroup.mk (vertex (1 : G) p j) : G ⧸ D.fam c.1) := by
      calc
        k • d = c.2 := hdc
        _ = QuotientGroup.mk (vertex k p j) := hjcos
        _ = k • (QuotientGroup.mk (vertex (1 : G) p j) : G ⧸ D.fam c.1) :=
          hvertex.symm
    have hd' : d =
        (QuotientGroup.mk (vertex (1 : G) p j) : G ⧸ D.fam c.1) := by
      have h := congrArg
        (fun e : G ⧸ D.fam c.1 => k⁻¹ • e) hkd
      simpa using h
    apply (mem_sepFinset D Dc h48 c.1 c'.2 1 z).mpr
    change (QuotientGroup.mk (vertex (1 : G) p j) : G ⧸ D.fam c.1) ∈
      sepSet D c.1 Dc 1 z
    rwa [← hd']
  have hjAt : PenetratesAt D c.1 Dc 1 p j c'.2 := by
    exact ⟨⟨j', hjcomp⟩, rfl⟩
  have hidxj : index c' = j :=
    penetratesAt_unique hp (c := c'.2) (hindex_spec c' hc'A) hjAt
  refine ⟨c', hc'A, (vertex (1 : G) p (index c))⁻¹ * vertex k p j, ?_, ?_⟩
  · exact Set.mem_iUnion.mpr ⟨c.1, hball⟩
  · change k = vertex (1 : G) p (index c) *
      ((vertex (1 : G) p (index c))⁻¹ * vertex k p j) *
        (vertex (1 : G) p (index c'))⁻¹
    rw [hidxj, ← hvertexG]
    group

/-- The exact remaining geometry of Lemma 5.11: construct the three pieces of
the local four-gon estimate (38). -/
def Lemma511Geometry [Fintype Λ] (D : RelGenSet G Λ) (Dc : ℕ) : Prop :=
  Lemma511FourGonAlternative D Dc

/-- A nonempty finite set of at most `n` elements can be enumerated by
`Fin n`.  The unused indices are filled with one element of the set. -/
theorem exists_fin_enumeration_of_nonempty {α : Type*} (A : Finset α)
    (hA : A.Nonempty) {n : ℕ} (hcard : A.card ≤ n) :
    ∃ e : Fin n → α, ∀ a ∈ A, ∃ i : Fin n, e i = a := by
  classical
  obtain ⟨a₀, ha₀⟩ := hA
  let eA : ↥A ≃ Fin (Fintype.card ↥A) := Fintype.equivFin ↥A
  have hcard' : Fintype.card ↥A ≤ n := by
    simpa using hcard
  let e : Fin n → α := fun i =>
    if hi : i.val < Fintype.card ↥A then
      ((eA.symm ⟨i.val, hi⟩ : ↥A) : α)
    else a₀
  refine ⟨e, ?_⟩
  intro a ha
  let aa : ↥A := ⟨a, ha⟩
  let j : Fin (Fintype.card ↥A) := eA aa
  have hjn : j.val < n := lt_of_lt_of_le j.isLt hcard'
  refine ⟨⟨j.val, hjn⟩, ?_⟩
  rw [show e ⟨j.val, hjn⟩ =
      if hj : j.val < Fintype.card ↥A then
        ((eA.symm ⟨j.val, hj⟩ : ↥A) : α) else a₀ from rfl,
    dif_pos j.isLt]
  have hfin : (⟨j.val, j.isLt⟩ : Fin (Fintype.card ↥A)) = j := Fin.ext rfl
  rw [hfin]
  exact congrArg Subtype.val (eA.symm_apply_apply aa)

/-- **The setwise Lemma 4.9 and equation (38) imply the entrance encoding.**

This proves all of Lemma 5.11 except the two geometric inputs named in the
hypotheses.  In particular equation (37), the choice of a shared coset outside
`S(1,k;D)`, and the uniform `3R` enumeration are no longer part of the debt. -/
theorem entranceEncoding_of_sharedGap [Fintype Λ]
    (D Y : RelGenSet G Λ) (Dc : ℕ)
    (h48 : ∀ lam : Λ, LemmaFourEight D lam Dc)
    (h49 : LemmaFourNineCover D Dc h48)
    (hdist : ∀ f g : G, wordDist Y.alphabet.carrier f g
      ≤ 2 * (∑ lam : Λ, sepCard D lam Dc f g) + 1)
    (hsle : ∀ f g : G, (∑ lam : Λ, sepCard D lam Dc f g)
      ≤ 3 * wordDist Y.alphabet.carrier f g)
    (hgap : Lemma511SharedGap D Y Dc h48) :
    Lemma511EntranceEncoding D Y Dc := by
  intro m z hz
  obtain ⟨entrance, hentrance⟩ := hgap m z hz
  let A := sepFinset D Dc h48 1 z
  let E : Finset G := A.image entrance
  have hAcard : A.card ≤ 3 * (18 * m + 11) := by
    have h := hsle 1 z
    rw [← card_sepFinset D Dc h48, hz] at h
    exact h
  have hAnonempty : A.Nonempty := by
    by_contra hne
    have hzero : A.card = 0 := Finset.card_eq_zero.mpr (Finset.not_nonempty_iff_eq_empty.mp hne)
    have h := hdist 1 z
    rw [hz, ← card_sepFinset D Dc h48, hzero] at h
    omega
  have hEnonempty : E.Nonempty := by
    obtain ⟨c, hc⟩ := hAnonempty
    refine ⟨entrance c, ?_⟩
    change entrance c ∈ A.image entrance
    exact Finset.mem_image.mpr ⟨c, hc, rfl⟩
  have hEcard : E.card ≤ 3 * (18 * m + 11) := by
    apply le_trans (b := A.card)
    · change (A.image entrance).card ≤ A.card
      exact Finset.card_image_le
    · exact hAcard
  obtain ⟨enum, henum⟩ := exists_fin_enumeration_of_nonempty E hEnonempty hEcard
  refine ⟨enum, ?_⟩
  intro k hk
  let B := sepFinset D Dc h48 k (k * z)
  let P := sepFinset D Dc h48 1 k
  have hshared : 3 * m + 1 ≤ (A ∩ B).card :=
    card_sharedSeparators_lower_bound D Y Dc h48 h49 hdist hsle m z k hz hk
  have hPcard : P.card ≤ 3 * m := by
    have h := hsle 1 k
    rw [← card_sepFinset D Dc h48] at h
    exact le_trans h (Nat.mul_le_mul_left 3 hk.1)
  have hex : ∃ c, c ∈ A ∩ B ∧ c ∉ P := by
    by_contra hnone
    have hsub : A ∩ B ⊆ P := by
      intro c hc
      by_contra hcP
      exact hnone ⟨c, hc, hcP⟩
    have hle := Finset.card_le_card hsub
    omega
  obtain ⟨c, hc, hcP⟩ := hex
  obtain ⟨c', hc'A, a, ha, hka⟩ :=
    hentrance k hk c (Finset.mem_inter.mp hc).1 (Finset.mem_inter.mp hc).2 hcP
  have hcent : entrance c ∈ E :=
    Finset.mem_image.mpr ⟨c, (Finset.mem_inter.mp hc).1, rfl⟩
  have hc'ent : entrance c' ∈ E :=
    Finset.mem_image.mpr ⟨c', hc'A, rfl⟩
  obtain ⟨i, hi⟩ := henum (entrance c) hcent
  obtain ⟨j, hj⟩ := henum (entrance c') hc'ent
  exact ⟨i, j, a, ha, by simpa [hi, hj] using hka⟩

end
end OsinComponents
end GGT
end GroupApproximation
