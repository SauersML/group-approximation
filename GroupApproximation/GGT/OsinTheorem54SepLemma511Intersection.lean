import GroupApproximation.GGT.OsinTheorem54SepLemma49
import GroupApproximation.GGT.OsinTheorem54SepLemma511Count

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

/-- The exact remaining geometry of Lemma 5.11: setwise Lemma 4.9 and the
entrance-gap estimate (38), at the already proved Lemma 4.8 interface. -/
def Lemma511Geometry [Fintype Λ] (D Y : RelGenSet G Λ) (Dc : ℕ) : Prop :=
  ∃ h48 : ∀ lam : Λ, LemmaFourEight D lam Dc,
    LemmaFourNineCover D Dc h48 ∧ Lemma511SharedGap D Y Dc h48

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
