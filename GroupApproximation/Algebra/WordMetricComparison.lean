import GroupApproximation.Algebra.WordMetric

/-!
# Comparing alphabets, and geodesic words

`Algebra/HyperbolicGroup.lean` defines hyperbolicity against *some* finite
symmetric generating set and records, in its docstring, the theorem it does not
prove: that the choice does not matter.  This module supplies the two things a
proof of that theorem starts from, and stops exactly where the missing input
begins.

## Comparing alphabets

`exists_wordNorm_le_mul` --- for finite symmetric generating sets `S` and `T`,
the word length of `T` is bounded by a constant multiple of the word length of
`S`, the constant being the largest `T`-length of a letter of `S`.
`exists_bilipschitz` runs that in both directions: the two word metrics are
bi-Lipschitz equivalent.

**This does not transfer hyperbolicity, and no claim here says it does.**  The
four-point condition is not a bi-Lipschitz invariant of an arbitrary metric
space; it becomes one for spaces that are geodesic, or coarsely so, and that
implication is the stability of quasi-geodesics --- the Morse lemma.  What is
proved here is the elementary half, which is the half that needs no geometry.

## Geodesic words

A word is *geodesic* when its length is the word length of the element it
spells.  `IsGeodesicWord` names that, `exists_isGeodesicWord` says every element
has one, and `isGeodesicWord_take`/`isGeodesicWord_drop` are the subword
property: every initial and every final segment of a geodesic word is itself
geodesic, and initial segments march out at unit speed
(`wordNorm_prod_take`).  These are the combinatorial geodesics of the Cayley
graph, stated without leaving the list model, and they are what a Morse-lemma
development would be about.  `wordDist_prod_append` is the statement that makes
them geodesics: a geodesic word is an isometric embedding of an interval.
-/

namespace GroupApproximation
namespace WordMetric

universe u

variable {G : Type u} [Group G]

/-! ## Subadditivity along a word -/

/-- The word length of a product is at most the sum of the word lengths of the
factors. -/
theorem wordNorm_prod_le {T : Set G} (hT : IsSymmetricGeneratingSet T) :
    ∀ l : List G, wordNorm T l.prod ≤ (l.map (wordNorm T)).sum := by
  intro l
  induction l with
  | nil => simp [wordNorm_one]
  | cons a t ih =>
      have h := wordNorm_mul_le hT a t.prod
      simp only [List.prod_cons, List.map_cons, List.sum_cons]
      omega

/-- A list of naturals bounded entrywise has its sum bounded by the obvious
product. -/
theorem sum_le_length_mul : ∀ (l : List ℕ) (C : ℕ), (∀ x ∈ l, x ≤ C) →
    l.sum ≤ l.length * C := by
  intro l C
  induction l with
  | nil => intro _; simp
  | cons a t ih =>
      intro h
      have ha : a ≤ C := h a (by simp)
      have ht : ∀ x ∈ t, x ≤ C := fun x hx => h x (by simp [hx])
      have hsum := ih ht
      simp only [List.sum_cons, List.length_cons]
      calc a + t.sum ≤ C + t.length * C := Nat.add_le_add ha hsum
        _ = (t.length + 1) * C := by ring

/-! ## Comparing two alphabets -/

/-- **Two finite symmetric generating sets have comparable word lengths.**  The
constant is the largest `T`-length of a letter of `S`: spell `g` by a shortest
`S`-word and spell each of its letters in `T`. -/
theorem exists_wordNorm_le_mul (S T : Finset G)
    (hS : IsSymmetricGeneratingSet (S : Set G))
    (hT : IsSymmetricGeneratingSet (T : Set G)) :
    ∃ C : ℕ, ∀ g : G, wordNorm (T : Set G) g ≤ C * wordNorm (S : Set G) g := by
  classical
  refine ⟨(S.sup fun s => wordNorm (T : Set G) s), fun g => ?_⟩
  obtain ⟨l, hl, hlen⟩ := exists_isWord_length_eq hS g
  have hbound : ∀ x ∈ l.map (wordNorm (T : Set G)),
      x ≤ (S.sup fun s => wordNorm (T : Set G) s) := by
    intro x hx
    simp only [List.mem_map] at hx
    obtain ⟨y, hy, rfl⟩ := hx
    exact Finset.le_sup (f := fun s => wordNorm (T : Set G) s)
      (Finset.mem_coe.mp (hl.letters y hy))
  calc wordNorm (T : Set G) g = wordNorm (T : Set G) l.prod := by rw [hl.prod_eq]
    _ ≤ (l.map (wordNorm (T : Set G))).sum := wordNorm_prod_le hT l
    _ ≤ (l.map (wordNorm (T : Set G))).length *
          (S.sup fun s => wordNorm (T : Set G) s) := sum_le_length_mul _ _ hbound
    _ = (S.sup fun s => wordNorm (T : Set G) s) * wordNorm (S : Set G) g := by
        rw [List.length_map, hlen]
        ring

/-- **The word metrics of two finite symmetric generating sets are bi-Lipschitz
equivalent.**  One positive constant serves in both directions. -/
theorem exists_bilipschitz (S T : Finset G)
    (hS : IsSymmetricGeneratingSet (S : Set G))
    (hT : IsSymmetricGeneratingSet (T : Set G)) :
    ∃ C : ℕ, 0 < C ∧ ∀ x y : G,
      wordDist (T : Set G) x y ≤ C * wordDist (S : Set G) x y ∧
        wordDist (S : Set G) x y ≤ C * wordDist (T : Set G) x y := by
  obtain ⟨C₁, h₁⟩ := exists_wordNorm_le_mul S T hS hT
  obtain ⟨C₂, h₂⟩ := exists_wordNorm_le_mul T S hT hS
  refine ⟨max 1 (max C₁ C₂), by omega, fun x y => ?_⟩
  have e₁ := h₁ (x⁻¹ * y)
  have e₂ := h₂ (x⁻¹ * y)
  have hd₁ : wordDist (T : Set G) x y = wordNorm (T : Set G) (x⁻¹ * y) := rfl
  have hd₂ : wordDist (S : Set G) x y = wordNorm (S : Set G) (x⁻¹ * y) := rfl
  rw [hd₁, hd₂]
  constructor
  · exact le_trans e₁ (Nat.mul_le_mul (by omega) (le_refl _))
  · exact le_trans e₂ (Nat.mul_le_mul (by omega) (le_refl _))

/-! ## Geodesic words -/

/-- A **geodesic word**: one whose length is the word length of the element it
spells.  This is a geodesic of the Cayley graph, in the list model. -/
structure IsGeodesicWord (S : Set G) (l : List G) (g : G) : Prop where
  /-- It spells `g`. -/
  isWord : IsWord S l g
  /-- It is as short as possible. -/
  length_eq : l.length = wordNorm S g

/-- Every element of a group with a symmetric generating set is spelled by a
geodesic word. -/
theorem exists_isGeodesicWord {S : Set G} (hS : IsSymmetricGeneratingSet S) (g : G) :
    ∃ l : List G, IsGeodesicWord S l g := by
  obtain ⟨l, hl, hlen⟩ := exists_isWord_length_eq hS g
  exact ⟨l, hl, hlen⟩

omit [Group G] in
/-- Letters of an initial segment are letters. -/
theorem mem_of_mem_take {l : List G} {n : ℕ} {x : G} (hx : x ∈ l.take n) : x ∈ l := by
  have h : x ∈ l.take n ++ l.drop n := List.mem_append_left _ hx
  rwa [List.take_append_drop] at h

omit [Group G] in
/-- Letters of a final segment are letters. -/
theorem mem_of_mem_drop {l : List G} {n : ℕ} {x : G} (hx : x ∈ l.drop n) : x ∈ l := by
  have h : x ∈ l.take n ++ l.drop n := List.mem_append_right _ hx
  rwa [List.take_append_drop] at h

/-- An initial segment of a word is a word for the element it spells. -/
theorem isWord_take {S : Set G} {l : List G} {g : G} (h : IsWord S l g) (n : ℕ) :
    IsWord S (l.take n) (l.take n).prod :=
  ⟨fun x hx => h.letters x (mem_of_mem_take hx), rfl⟩

/-- A final segment of a word is a word for the element it spells. -/
theorem isWord_drop {S : Set G} {l : List G} {g : G} (h : IsWord S l g) (n : ℕ) :
    IsWord S (l.drop n) (l.drop n).prod :=
  ⟨fun x hx => h.letters x (mem_of_mem_drop hx), rfl⟩

/-- **Initial segments of a geodesic word march out at unit speed.**  If a
prefix spelled a shorter element, splicing that shorter spelling in front of the
remaining letters would shorten the whole word, which is geodesic. -/
theorem wordNorm_prod_take {S : Set G} {l : List G} {g : G}
    (hS : IsSymmetricGeneratingSet S) (h : IsGeodesicWord S l g) (n : ℕ) :
    wordNorm S (l.take n).prod = (l.take n).length := by
  refine le_antisymm (wordNorm_le_length (isWord_take h.isWord n)) ?_
  by_contra hlt
  push Not at hlt
  obtain ⟨m, hm, hmlen⟩ := exists_isWord_length_eq hS (l.take n).prod
  have hg : (l.take n).prod * (l.drop n).prod = g := by
    rw [← List.prod_append, List.take_append_drop, h.isWord.prod_eq]
  have hcat : IsWord S (m ++ l.drop n) g := by
    have hstep := isWord_append hm (isWord_drop h.isWord n)
    rwa [hg] at hstep
  have hle := wordNorm_le_length hcat
  rw [List.length_append, hmlen, ← h.length_eq] at hle
  have hsplit : (l.take n).length + (l.drop n).length = l.length := by
    rw [← List.length_append, List.take_append_drop]
  omega

/-- Final segments march out at unit speed too, by the mirror argument. -/
theorem wordNorm_prod_drop {S : Set G} {l : List G} {g : G}
    (hS : IsSymmetricGeneratingSet S) (h : IsGeodesicWord S l g) (n : ℕ) :
    wordNorm S (l.drop n).prod = (l.drop n).length := by
  refine le_antisymm (wordNorm_le_length (isWord_drop h.isWord n)) ?_
  by_contra hlt
  push Not at hlt
  obtain ⟨m, hm, hmlen⟩ := exists_isWord_length_eq hS (l.drop n).prod
  have hg : (l.take n).prod * (l.drop n).prod = g := by
    rw [← List.prod_append, List.take_append_drop, h.isWord.prod_eq]
  have hcat : IsWord S (l.take n ++ m) g := by
    have hstep := isWord_append (isWord_take h.isWord n) hm
    rwa [hg] at hstep
  have hle := wordNorm_le_length hcat
  rw [List.length_append, hmlen, ← h.length_eq] at hle
  have hsplit : (l.take n).length + (l.drop n).length = l.length := by
    rw [← List.length_append, List.take_append_drop]
  omega

/-- **The subword property.**  Every initial segment of a geodesic word is
itself geodesic. -/
theorem isGeodesicWord_take {S : Set G} {l : List G} {g : G}
    (hS : IsSymmetricGeneratingSet S) (h : IsGeodesicWord S l g) (n : ℕ) :
    IsGeodesicWord S (l.take n) (l.take n).prod :=
  ⟨isWord_take h.isWord n, (wordNorm_prod_take hS h n).symm⟩

/-- ... and so is every final segment. -/
theorem isGeodesicWord_drop {S : Set G} {l : List G} {g : G}
    (hS : IsSymmetricGeneratingSet S) (h : IsGeodesicWord S l g) (n : ℕ) :
    IsGeodesicWord S (l.drop n) (l.drop n).prod :=
  ⟨isWord_drop h.isWord n, (wordNorm_prod_drop hS h n).symm⟩

/-- **A geodesic word is an isometric embedding of an interval.**  The distance
from the element spelled by an initial segment to the element spelled by the
whole word is exactly the number of letters left over --- geodesic words move at
unit speed, which is what makes them geodesics and what a Morse-lemma argument
would quantify over. -/
theorem wordDist_prod_append {S : Set G} {l₁ l₂ : List G} {g : G}
    (hS : IsSymmetricGeneratingSet S) (h : IsGeodesicWord S (l₁ ++ l₂) g) :
    wordDist S l₁.prod (l₁ ++ l₂).prod = l₂.length := by
  have hsplit : (l₁ ++ l₂).prod = l₁.prod * l₂.prod := List.prod_append
  have hleft : IsWord S l₁ l₁.prod :=
    ⟨fun x hx => h.isWord.letters x (List.mem_append_left _ hx), rfl⟩
  have hright : IsWord S l₂ l₂.prod :=
    ⟨fun x hx => h.isWord.letters x (List.mem_append_right _ hx), rfl⟩
  have hcancel : l₁.prod⁻¹ * (l₁ ++ l₂).prod = l₂.prod := by
    rw [hsplit, inv_mul_cancel_left]
  have hd : wordDist S l₁.prod (l₁ ++ l₂).prod = wordNorm S l₂.prod := by
    show wordNorm S (l₁.prod⁻¹ * (l₁ ++ l₂).prod) = wordNorm S l₂.prod
    rw [hcancel]
  rw [hd]
  refine le_antisymm (wordNorm_le_length hright) ?_
  by_contra hlt
  push Not at hlt
  obtain ⟨m, hm, hmlen⟩ := exists_isWord_length_eq hS l₂.prod
  have hcat : IsWord S (l₁ ++ m) g := by
    have hstep := isWord_append hleft hm
    rwa [← hsplit, h.isWord.prod_eq] at hstep
  have hle := wordNorm_le_length hcat
  rw [List.length_append, hmlen, ← h.length_eq, List.length_append] at hle
  omega

end WordMetric
end GroupApproximation
