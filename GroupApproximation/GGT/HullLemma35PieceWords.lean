import GroupApproximation.GGT.HullLemma35Transitive
import GroupApproximation.GGT.HullLemma35Expansion
import GroupApproximation.Algebra.HyperbolicSlimTriangles
import GroupApproximation.Meta.AxiomGuard

/-!
# Hull's Lemma 3.5: expanding the peripheral letters into the subfamilies

The manuscript's paragraph on Fournier-Facio's group (section `sec:torsion-free`, tex 1680-1684)
says:

> The group $G_0$ is obtained there as a common quotient of two finitely generated acylindrically
> hyperbolic groups by Hull's theorem~\cite[Corollary~7.4]{Hull}, which allows the quotient to be
> chosen acylindrically hyperbolic; we take $G_0$ to be such a quotient.

Hull's proof of Corollary 7.4 uses his Lemma 3.5 (`PrintedHullLemma35`).  Its hyperbolicity clause
expands a geodesic word of `D` letter by letter into a word over the alphabet of
`transitiveRelGenSet D E`: a letter of the proper part of `D.base` stays, and a letter `h` of `H i`
becomes a shortest word of `E i` spelling `h` (`transEx`).  This module records:

* `isBetween_mul_prod_take` — the prefixes of a shortest word lie between its ends;
* `transEx_prod`, `transEx_mem` — the expansion spells each letter with transitive letters;
* `properRelGenSet` — `D` over the proper part of its base: its base is inversion-closed, its
  alphabet is that of `D`, and its relative balls are smaller;
* `exists_pieceWord_length_le`, `length_transEx_le_of_wordNorm_le_one` — over finitely many members
  the expansions of a relative ball, and of short letters, have bounded length.
-/

namespace GroupApproximation
namespace GGT
namespace HullLemma35

open GroupApproximation.WordMetric

universe u v w

section Geodesic

variable {H : Type u} [Group H]

/-- **A shortest word** of a symmetric generating set `A` spelling `g`. -/
noncomputable def geodList {A : Set H} (hA : IsSymmetricGeneratingSet A) (g : H) : List H :=
  Classical.choose (exists_isWord_length_eq hA g)

theorem geodList_spec {A : Set H} (hA : IsSymmetricGeneratingSet A) (g : H) :
    IsWord A (geodList hA g) g ∧ (geodList hA g).length = wordNorm A g :=
  Classical.choose_spec (exists_isWord_length_eq hA g)

/-- **The prefixes of a shortest word lie between its ends**, at the distance of their length. -/
theorem isBetween_mul_prod_take {A : Set H} (hA : IsSymmetricGeneratingSet A) {l : List H} {g : H}
    (hl : IsWord A l g) (hlen : l.length = wordNorm A g) (X : H) {m : ℕ} (hm : m ≤ l.length) :
    Hyperbolic.IsBetween A X (X * (l.take m).prod) (X * g) ∧
      wordDist A X (X * (l.take m).prod) = m := by
  have hp : IsWord A (l.take m) (l.take m).prod :=
    ⟨fun x hx => hl.letters x (List.take_subset m l hx), rfl⟩
  have hr : IsWord A (l.drop m) (l.drop m).prod :=
    ⟨fun x hx => hl.letters x (List.drop_subset m l hx), rfl⟩
  have hsplit : (l.take m).prod * (l.drop m).prod = g := by
    rw [List.prod_take_mul_prod_drop, hl.prod_eq]
  have hnp := wordNorm_le_length hp
  have hnr := wordNorm_le_length hr
  rw [List.length_take_of_le hm] at hnp
  rw [List.length_drop] at hnr
  have h₁ : wordDist A X (X * (l.take m).prod) = wordNorm A (l.take m).prod := by
    unfold wordDist
    rw [inv_mul_cancel_left]
  have h₂ : wordDist A (X * (l.take m).prod) (X * g) = wordNorm A (l.drop m).prod := by
    have e : (X * (l.take m).prod)⁻¹ * (X * g) = (l.drop m).prod := by
      rw [← hsplit]
      group
    unfold wordDist
    rw [e]
  have h₃ : wordDist A X (X * g) = wordNorm A g := by
    unfold wordDist
    rw [inv_mul_cancel_left]
  have htri := wordDist_triangle hA X (X * (l.take m).prod) (X * g)
  rw [h₁, h₂, h₃] at htri
  refine ⟨?_, ?_⟩
  · show wordDist A X _ + wordDist A _ _ = wordDist A X _
    rw [h₁, h₂, h₃]
    omega
  · rw [h₁]
    omega

end Geodesic

section Pieces

variable {G : Type u} [Group G] {Λ : Type v} {M : Λ → Type w}

/-! ## `D` over the proper part of its base -/

/-- `D.base` and its proper part give the same alphabet. -/
theorem properBase_union_eq (D : RelGenSet G Λ) :
    RelHyp.properBase D ∪ ⋃ lam : Λ, ((D.fam lam : Subgroup G) : Set G) =
      D.base ∪ ⋃ lam : Λ, ((D.fam lam : Subgroup G) : Set G) :=
  Set.Subset.antisymm (Set.union_subset_union_left _ (RelHyp.properBase_subset_base D))
    (Set.union_subset (RelHyp.base_subset_properBase_union D) Set.subset_union_right)

/-- **`D` over the proper part of its base.** -/
def properRelGenSet (D : RelGenSet G Λ) : RelGenSet G Λ where
  base := RelHyp.properBase D
  fam := D.fam
  symmetricGenerating := by
    rw [properBase_union_eq D]
    exact D.symmetricGenerating

theorem properRelGenSet_base_inv (D : RelGenSet G Λ) :
    ∀ x ∈ (properRelGenSet D).base, x⁻¹ ∈ (properRelGenSet D).base :=
  fun _ hx => RelHyp.properBase_inv D hx

theorem properRelGenSet_alphabet_carrier (D : RelGenSet G Λ) :
    (properRelGenSet D).alphabet.carrier = D.alphabet.carrier :=
  properBase_union_eq D

theorem properRelGenSet_relBall_subset (D : RelGenSet G Λ) (lam : Λ) (n : ℕ) :
    (properRelGenSet D).relBall lam n ⊆ D.relBall lam n := by
  rintro h ⟨hh, w, hw, hval, havoid, hlen⟩
  refine ⟨hh, w, fun a ha => ?_, hval, havoid, hlen⟩
  cases a with
  | base x => exact RelHyp.properBase_subset_base D (hw _ ha)
  | comp mu e => exact hw _ ha

/-- **`D` over its proper base is hyperbolically embedded when `D` is.** -/
theorem isHyperbolicallyEmbedded_properRelGenSet (D : RelGenSet G Λ)
    (hD : D.IsHyperbolicallyEmbedded) : (properRelGenSet D).IsHyperbolicallyEmbedded :=
  ⟨RelHyp.exists_isHyperbolicSpace_of_alphabet_eq
      (OsinComponents.alphabet_eq_of_carrier_eq (properRelGenSet_alphabet_carrier D)) hD.hyperbolic,
    fun lam n => (hD.locallyFinite lam n).subset (properRelGenSet_relBall_subset D lam n)⟩

/-- A member of two different members of the family lies in the relative ball of radius `1`. -/
theorem mem_relBall_one_of_ne (D : RelGenSet G Λ) {lam mu : Λ} (hne : mu ≠ lam) {e : G}
    (hl : e ∈ D.fam lam) (hm : e ∈ D.fam mu) : e ∈ D.relBall lam 1 := by
  refine RelGenSet.mem_relBall.mpr ⟨hl, [RelLetter.comp mu e], ?_, ?_, ?_, by simp⟩
  · intro a ha
    obtain rfl := List.mem_singleton.mp ha
    exact hm
  · show ([RelLetter.comp mu e].map RelLetter.val).prod = e
    simp [RelLetter.val]
  · exact ⟨fun h => hne h.1, trivial⟩

/-! ## The expansion -/

open Classical in
/-- **The expansion of a member letter**: a shortest word of `E lam` spelling `e`, carried into
`G`.  Outside `H lam` it is the one-letter word; no letter of `D` uses it. -/
noncomputable def pieceWord (D : RelGenSet G Λ) (E : ∀ i : Λ, RelGenSet (D.fam i) (M i)) (lam : Λ)
    (e : G) : List G :=
  if he : e ∈ D.fam lam then
    (geodList (E lam).alphabet.symmetricGenerating ⟨e, he⟩).map (D.fam lam).subtype
  else [e]

/-- **The expansion of the letters of `D`** into the transitive alphabet. -/
noncomputable def transEx (D : RelGenSet G Λ) (E : ∀ i : Λ, RelGenSet (D.fam i) (M i)) :
    RelLetter G Λ → List G
  | RelLetter.base b => [b]
  | RelLetter.comp lam e => pieceWord D E lam e

theorem transEx_base (D : RelGenSet G Λ) (E : ∀ i : Λ, RelGenSet (D.fam i) (M i)) (b : G) :
    transEx D E (RelLetter.base b) = [b] := rfl

theorem transEx_comp (D : RelGenSet G Λ) (E : ∀ i : Λ, RelGenSet (D.fam i) (M i)) (lam : Λ)
    (e : G) : transEx D E (RelLetter.comp lam e) = pieceWord D E lam e := rfl

theorem pieceWord_of_mem (D : RelGenSet G Λ) (E : ∀ i : Λ, RelGenSet (D.fam i) (M i)) {lam : Λ}
    {e : G} (he : e ∈ D.fam lam) :
    pieceWord D E lam e =
      (geodList (E lam).alphabet.symmetricGenerating ⟨e, he⟩).map (D.fam lam).subtype := by
  unfold pieceWord
  rw [dif_pos he]

theorem pieceWord_prod (D : RelGenSet G Λ) (E : ∀ i : Λ, RelGenSet (D.fam i) (M i)) (lam : Λ)
    (e : G) : (pieceWord D E lam e).prod = e := by
  by_cases he : e ∈ D.fam lam
  · have h := MonoidHom.map_list_prod (D.fam lam).subtype
      (geodList (E lam).alphabet.symmetricGenerating ⟨e, he⟩)
    rw [(geodList_spec (E lam).alphabet.symmetricGenerating ⟨e, he⟩).1.prod_eq] at h
    rw [pieceWord_of_mem D E he, ← h]
    rfl
  · unfold pieceWord
    rw [dif_neg he, List.prod_singleton]

/-- **The expansion spells each letter.** -/
theorem transEx_prod (D : RelGenSet G Λ) (E : ∀ i : Λ, RelGenSet (D.fam i) (M i)) :
    ∀ a : RelLetter G Λ, (transEx D E a).prod = a.val
  | RelLetter.base b => by
      rw [transEx_base]
      exact List.prod_singleton
  | RelLetter.comp lam e => pieceWord_prod D E lam e

/-- **The expansion uses transitive letters** on the letters of `D` over its proper base. -/
theorem transEx_mem (D : RelGenSet G Λ) (E : ∀ i : Λ, RelGenSet (D.fam i) (M i)) :
    ∀ a : RelLetter G Λ, (properRelGenSet D).IsLetter a →
      ∀ s ∈ transEx D E a, s ∈ (transitiveRelGenSet D E).alphabet.carrier
  | RelLetter.base b, hb, s, hs => by
      rw [transEx_base] at hs
      obtain rfl : s = b := List.mem_singleton.mp hs
      exact Or.inl (Or.inl hb)
  | RelLetter.comp lam e, he, s, hs => by
      have he' : e ∈ D.fam lam := he
      rw [transEx_comp, pieceWord_of_mem D E he'] at hs
      obtain ⟨t, ht, rfl⟩ := List.mem_map.mp hs
      rcases (geodList_spec (E lam).alphabet.symmetricGenerating ⟨e, he'⟩).1.letters t ht with
          hb | hf
      · exact Or.inl (Or.inr (Set.mem_iUnion.mpr ⟨lam, ⟨t, hb, rfl⟩⟩))
      · obtain ⟨j, hj⟩ := Set.mem_iUnion.mp hf
        exact Or.inr (Set.mem_iUnion.mpr ⟨⟨lam, j⟩, ⟨t, hj, rfl⟩⟩)

theorem length_pieceWord_of_mem (D : RelGenSet G Λ) (E : ∀ i : Λ, RelGenSet (D.fam i) (M i))
    {lam : Λ} {e : G} (he : e ∈ D.fam lam) :
    (pieceWord D E lam e).length = wordNorm (E lam).alphabet.carrier ⟨e, he⟩ := by
  rw [pieceWord_of_mem D E he, List.length_map,
    (geodList_spec (E lam).alphabet.symmetricGenerating ⟨e, he⟩).2]

/-- The prefixes of the expansion of a member letter are the images of prefixes of a shortest word
of `E lam`. -/
theorem prod_take_pieceWord (D : RelGenSet G Λ) (E : ∀ i : Λ, RelGenSet (D.fam i) (M i))
    {lam : Λ} {e : G} (he : e ∈ D.fam lam) (s : ℕ) :
    ((pieceWord D E lam e).take s).prod =
      (D.fam lam).subtype ((geodList (E lam).alphabet.symmetricGenerating ⟨e, he⟩).take s).prod := by
  rw [pieceWord_of_mem D E he, ← List.map_take, MonoidHom.map_list_prod]

/-- A member letter has transitive length at most the length of its expansion. -/
theorem wordNorm_le_length_pieceWord (D : RelGenSet G Λ) (E : ∀ i : Λ, RelGenSet (D.fam i) (M i))
    {lam : Λ} {e : G} (he : e ∈ D.fam lam) :
    wordNorm (transitiveRelGenSet D E).alphabet.carrier e ≤ (pieceWord D E lam e).length :=
  wordNorm_le_length ⟨transEx_mem D E (RelLetter.comp lam e) he, pieceWord_prod D E lam e⟩

/-! ## Bounded expansions -/

/-- **Bounded expansions of a relative ball.**  Over finitely many members with finite relative
balls, the expansions of the elements of a ball of radius `n` have bounded length. -/
theorem exists_pieceWord_length_le (D : RelGenSet G Λ) (E : ∀ i : Λ, RelGenSet (D.fam i) (M i))
    [Finite Λ] (hloc : ∀ (lam : Λ) (n : ℕ), (D.relBall lam n).Finite) (n : ℕ) :
    ∃ T : ℕ, ∀ (lam : Λ) (e : G), e ∈ D.relBall lam n → (pieceWord D E lam e).length ≤ T := by
  have hb : ∀ lam : Λ, ∃ B : ℕ, ∀ e ∈ D.relBall lam n, (pieceWord D E lam e).length ≤ B := by
    intro lam
    obtain ⟨B, hB⟩ := ((hloc lam n).image fun e => (pieceWord D E lam e).length).bddAbove
    exact ⟨B, fun e he => hB ⟨e, he, rfl⟩⟩
  choose B hB using hb
  obtain ⟨T, hT⟩ := (Set.finite_range B).bddAbove
  exact ⟨T, fun lam e he => le_trans (hB lam e he) (hT ⟨lam, rfl⟩)⟩

/-- A member of `H lam` spelled by one transitive letter is a letter of `E lam`, or lies in another
member and so in the relative ball of radius `1`. -/
theorem mem_alphabet_or_mem_relBall_one (D : RelGenSet G Λ)
    (E : ∀ i : Λ, RelGenSet (D.fam i) (M i)) {lam : Λ} {e : G} (he : e ∈ D.fam lam)
    (hS : e ∈ (transitiveRelGenSet D E).alphabet.carrier) :
    (⟨e, he⟩ : D.fam lam) ∈ (E lam).alphabet.carrier ∨ e ∈ D.relBall lam 1 := by
  rcases hS with (hp | hi) | hf
  · exact absurd he (RelHyp.properBase_disjoint_fam D lam hp)
  · obtain ⟨i, t, ht, rfl⟩ := Set.mem_iUnion.mp hi
    by_cases hil : i = lam
    · subst hil
      exact Or.inl (Or.inl ht)
    · exact Or.inr (mem_relBall_one_of_ne D hil he t.2)
  · obtain ⟨⟨i, j⟩, hp⟩ := Set.mem_iUnion.mp hf
    obtain ⟨t, ht, rfl⟩ := (show e ∈ transitiveFam D E ⟨i, j⟩ from hp)
    by_cases hil : i = lam
    · subst hil
      exact Or.inl (Or.inr (Set.mem_iUnion.mpr ⟨j, ht⟩))
    · exact Or.inr (mem_relBall_one_of_ne D hil he t.2)

/-- **Short letters have short expansions.**  A letter of `D` over its proper base spelling an
element of transitive length at most `1` expands to at most `T + 1` letters, when `T` bounds the
expansions of the relative balls of radius `1`. -/
theorem length_transEx_le_of_wordNorm_le_one (D : RelGenSet G Λ)
    (E : ∀ i : Λ, RelGenSet (D.fam i) (M i)) {T : ℕ}
    (hT : ∀ (lam : Λ) (e : G), e ∈ D.relBall lam 1 → (pieceWord D E lam e).length ≤ T) :
    ∀ a : RelLetter G Λ, (properRelGenSet D).IsLetter a →
      wordNorm (transitiveRelGenSet D E).alphabet.carrier a.val ≤ 1 →
        (transEx D E a).length ≤ T + 1
  | RelLetter.base b, _, _ => by
      rw [transEx_base, List.length_singleton]
      omega
  | RelLetter.comp lam e, he, hn => by
      have he' : e ∈ D.fam lam := he
      rw [transEx_comp]
      obtain ⟨l, hl, hlen⟩ :=
        exists_isWord_length_eq (transitiveRelGenSet D E).alphabet.symmetricGenerating e
      have hn' : l.length ≤ 1 := by
        rw [hlen]
        exact hn
      rcases l with _ | ⟨x, _ | ⟨y, l⟩⟩
      · have h1 : (⟨e, he'⟩ : D.fam lam) = 1 := Subtype.ext hl.prod_eq.symm
        rw [length_pieceWord_of_mem D E he', h1, wordNorm_one]
        omega
      · have hx : e ∈ (transitiveRelGenSet D E).alphabet.carrier := by
          rw [← hl.prod_eq, List.prod_singleton]
          exact hl.letters x (List.mem_singleton_self x)
        rcases mem_alphabet_or_mem_relBall_one D E he' hx with hA | hB
        · rw [length_pieceWord_of_mem D E he']
          have h1 := wordNorm_le_one_of_mem hA
          omega
        · exact le_trans (hT lam e hB) (Nat.le_succ T)
      · rw [List.length_cons, List.length_cons] at hn'
        omega

end Pieces

end HullLemma35
end GGT
end GroupApproximation

#audit_axioms GroupApproximation.GGT.HullLemma35.isBetween_mul_prod_take
#audit_axioms GroupApproximation.GGT.HullLemma35.isHyperbolicallyEmbedded_properRelGenSet
#audit_axioms GroupApproximation.GGT.HullLemma35.transEx_mem
#audit_axioms GroupApproximation.GGT.HullLemma35.prod_take_pieceWord
#audit_axioms GroupApproximation.GGT.HullLemma35.exists_pieceWord_length_le
#audit_axioms GroupApproximation.GGT.HullLemma35.length_transEx_le_of_wordNorm_le_one
