import GroupApproximation.GGT.HullSCRelatorSeparation2ApplySpelling

/-!
# The quadrilateral's short sides

The separation hands the composition two elements, `y` and `z`, with
`wordNorm base y ≤ eps` and the same for `z`, and the quadrilateral wants them
as WORDS: two lists of base letters naming them, each of positive length,
whose values are short in the relative alphabet.

Both are read off the same padding.  `HullSC.exists_long_base_spelling_of_base_eq`
at `P := 1` applied to `y⁻¹` gives a base word for `y` of length at least one,
since padding is by a letter and its inverse and changes neither the value nor
its norm.  That is the whole of the `0 < |py|` clause the aligned closers ask
for, and it is why the degenerate cases `y = 1` and `z = 1` need no separate
treatment: the empty spelling is never the one taken.

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

/-- **A short element is a nonempty base word of the same relative norm.**

The quadrilateral's first and third sides, in the form its closers take them:
letters of the base, positive length, the right value, and a relative norm no
larger than the bound the separation gives. -/
theorem exists_side_spelling_of_base_eq {Λ : Type w} {D : GGT.RelGenSet G Λ}
    (hbase : D.base = A.alphabet.carrier) (hN : Suitable A.alphabet N)
    {y : G} {n : ℕ} (hy : wordNorm D.base y ≤ n) :
    ∃ py : List (GGT.RelLetter G Λ), 0 < py.length ∧
      (∀ x ∈ py, ∃ g : G, x = GGT.RelLetter.base g) ∧
        (∀ x ∈ py, D.IsLetter x) ∧ GGT.RelLetter.listVal py = y ∧
          wordNorm D.alphabet.carrier (GGT.RelLetter.listVal py) ≤ n := by
  obtain ⟨l, hlen, hlbase, hlprod⟩ :=
    exists_long_base_spelling_of_base_eq hbase hN y⁻¹ 1
  have hval : GGT.RelLetter.listVal
      (l.map (GGT.RelLetter.base : G → GGT.RelLetter G Λ)) = y := by
    rw [listVal_map_base, hlprod, inv_inv]
  refine ⟨l.map GGT.RelLetter.base, ?_, ?_, ?_, hval, ?_⟩
  · rw [List.length_map]
    omega
  · intro x hx
    obtain ⟨g, _hg, rfl⟩ := List.mem_map.mp hx
    exact ⟨g, rfl⟩
  · intro x hx
    obtain ⟨g, hg, rfl⟩ := List.mem_map.mp hx
    show g ∈ D.base
    exact hlbase g hg
  · rw [hval]
    have hS : IsSymmetricGeneratingSet D.base := by
      rw [hbase]
      exact A.alphabet.symmetricGenerating
    have hsub : D.base ⊆ D.alphabet.carrier := by
      show D.base ⊆ D.base ∪ ⋃ lam : Λ, (D.fam lam : Set G)
      exact Set.subset_union_left
    exact le_trans (wordNorm_mono hsub (wordLengths_nonempty hS y)) hy

/-- **The two-subgroup core's short sides.**  The form the composition takes
them in, with the base identified by `HullSC.HypEmbeddedCore₂.base_eq`. -/
theorem exists_side_spelling₂ (E : HypEmbeddedCore₂ A N)
    (hN : Suitable A.alphabet N) {y : G} {n : ℕ}
    (hy : wordNorm E.rel.base y ≤ n) :
    ∃ py : List (GGT.RelLetter G Bool), 0 < py.length ∧
      (∀ x ∈ py, ∃ g : G, x = GGT.RelLetter.base g) ∧
        (∀ x ∈ py, E.rel.IsLetter x) ∧ GGT.RelLetter.listVal py = y ∧
          wordNorm E.rel.alphabet.carrier (GGT.RelLetter.listVal py) ≤ n :=
  exists_side_spelling_of_base_eq E.base_eq hN hy

end ShortSide

end HullSC
end GroupApproximation
