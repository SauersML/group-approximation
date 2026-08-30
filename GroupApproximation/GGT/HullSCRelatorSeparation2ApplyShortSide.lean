import GroupApproximation.GGT.HullSCRelatorSeparation2ApplySpelling

/-!
# The quadrilateral's short sides

The separation hands the composition two elements, `y` and `z`, with
`wordNorm base y ≤ eps` and the same for `z`, and the quadrilateral wants them
as WORDS: two lists of base letters naming them, each of positive length,
whose values are short in the relative alphabet.

Both are read off the same padding.  `HullSC.exists_long_base_spelling_of_base_le`
at `P := 1` applied to `y⁻¹` gives a base word for `y` of length at least one,
since padding is by a letter and its inverse and changes neither the value nor
its norm.  That is the whole of the `0 < |py|` clause the aligned closers ask
for, and it is why the degenerate cases `y = 1` and `z = 1` need no separate
treatment: the empty spelling is never the one taken.

The length bound `|py| ≤ n + 2` is the other half, and it is what the four-gon's
quasi-geodesic clause is read from at the two short sides.  It needs the
spelling to be MINIMAL, which is why `exists_isWord_length_eq` is taken rather
than `exists_isWord`: the latter returns some word, and some word can be
arbitrarily long.

The norm clause goes the other way round and costs nothing: the pinning
estimate reads the RELATIVE norm of the short side's value, and the relative
alphabet contains the base, so `wordNorm_mono` turns the separation's base
bound into it.  Nothing here reads the length of a short side.
-/

namespace GroupApproximation
namespace HullSC

open GroupApproximation.HullGeometry
open GroupApproximation.WordMetric
open GroupApproximation.Manuscript.NonMF.TorsionFree

universe u w

section ShortSide

variable {G : Type u} [Group G] {A : HullGeneratingSet G} {N : Subgroup G}

/-- **A short element is a nonempty base word of bounded length and the same
relative norm.**

The quadrilateral's first and third sides, in the form its closers take them:
letters of the base, positive length, length at most `n + 2`, the right value,
and a relative norm no larger than the bound the separation gives.

The length bound is what the four-gon's quasi-geodesic clause is read from at
those two sides, so the spelling has to be a MINIMAL one --- `exists_isWord`
gives some word, and some word can be arbitrarily long.  Padding a minimal word
by a letter and its inverse costs exactly two. -/
theorem exists_side_spelling_of_base_le {Λ : Type w} {D : GGT.RelGenSet G Λ}
    (hS : IsSymmetricGeneratingSet D.base)
    (hle : A.alphabet.carrier ⊆ D.base) (hN : Suitable A.alphabet N)
    {y : G} {n : ℕ} (hy : wordNorm D.base y ≤ n) :
    ∃ py : List (GGT.RelLetter G Λ), 0 < py.length ∧ py.length ≤ n + 2 ∧
      (∀ x ∈ py, ∃ g : G, x = GGT.RelLetter.base g) ∧
        (∀ x ∈ py, D.IsLetter x) ∧ GGT.RelLetter.listVal py = y ∧
          wordNorm D.alphabet.carrier (GGT.RelLetter.listVal py) ≤ n := by
  obtain ⟨l, hl, hlen⟩ := exists_isWord_length_eq hS y
  obtain ⟨g, hg, hginv⟩ := exists_mem_base_of_base_le hle hN
  have hval : GGT.RelLetter.listVal
      ((g :: g⁻¹ :: l).map (GGT.RelLetter.base : G → GGT.RelLetter G Λ))
      = y := by
    rw [listVal_map_base, List.prod_cons, List.prod_cons, hl.prod_eq,
      mul_inv_cancel_left]
  refine ⟨(g :: g⁻¹ :: l).map GGT.RelLetter.base, ?_, ?_, ?_, ?_, hval, ?_⟩
  · rw [List.length_map, List.length_cons, List.length_cons]
    omega
  · rw [List.length_map, List.length_cons, List.length_cons]
    omega
  · intro x hx
    obtain ⟨a, _ha, rfl⟩ := List.mem_map.mp hx
    exact ⟨a, rfl⟩
  · intro x hx
    obtain ⟨a, ha, rfl⟩ := List.mem_map.mp hx
    show a ∈ D.base
    rcases List.mem_cons.mp ha with rfl | ha1
    · exact hg
    · rcases List.mem_cons.mp ha1 with rfl | ha2
      · exact hginv
      · exact hl.letters a ha2
  · rw [hval]
    have hsub : D.base ⊆ D.alphabet.carrier := by
      show D.base ⊆ D.base ∪ ⋃ lam : Λ, (D.fam lam : Set G)
      exact Set.subset_union_left
    exact le_trans (wordNorm_mono hsub (wordLengths_nonempty hS y)) hy

/-- **The two-subgroup core's short sides.**  The form the composition takes
them in, with the base containing Hull's alphabet by
`HullSC.HypEmbeddedCore₂.base_le`. -/
theorem exists_side_spelling₂ (E : HypEmbeddedCore₂ A N)
    (hN : Suitable A.alphabet N) {y : G} {n : ℕ}
    (hy : wordNorm E.rel.base y ≤ n) :
    ∃ py : List (GGT.RelLetter G Bool), 0 < py.length ∧ py.length ≤ n + 2 ∧
      (∀ x ∈ py, ∃ g : G, x = GGT.RelLetter.base g) ∧
        (∀ x ∈ py, E.rel.IsLetter x) ∧ GGT.RelLetter.listVal py = y ∧
          wordNorm E.rel.alphabet.carrier (GGT.RelLetter.listVal py) ≤ n :=
  exists_side_spelling_of_base_le (isSymmetricGeneratingSet_base₂ E) E.base_le
    hN hy

end ShortSide

end HullSC
end GroupApproximation
