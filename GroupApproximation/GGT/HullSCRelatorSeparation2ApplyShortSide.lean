import GroupApproximation.GGT.HullSCRelatorSeparation2ApplySpelling
import GroupApproximation.GGT.OsinGeodesicWord

/-!
# The quadrilateral's short sides

The published piece condition hands the composition two elements, `y` and
`z`, with relative-alphabet norm at most `eps`, and the quadrilateral wants
them as WORDS: two lists of relative letters naming them, each of positive
length.

Both are obtained by lifting a shortest word in the full relative alphabet.
A base letter and its inverse pad that lift to positive length without
changing its value.  This handles the degenerate cases `y = 1` and `z = 1`
uniformly.

The length bound `|py| ≤ n + 2` is the other half, and it is what the four-gon's
quasi-geodesic clause is read from at the two short sides.  It needs the
spelling to be MINIMAL, which is why `exists_isWord_length_eq` is taken rather
than `exists_isWord`: the latter returns some word, and some word can be
arbitrarily long.

This is exactly Osin Definition 4.1: the short words use the whole generating
alphabet `A`, not merely the relative base `X`.
-/

namespace GroupApproximation
namespace HullSC

open GroupApproximation.HullGeometry
open GroupApproximation.WordMetric

universe u w
open GroupApproximation.Manuscript.NonMF.TorsionFree

section ShortSide

variable {G : Type u} [Group G] {A : HullGeneratingSet G} {N : Subgroup G}

/-- **A short element is a nonempty relative word of bounded length.**

The quadrilateral's first and third sides, in the form its closers take them:
legal relative letters, positive length, length at most `n + 2`, the right
value, and a relative norm no larger than the bound the piece gives.

The length bound is what the four-gon's quasi-geodesic clause is read from at
those two sides, so the spelling has to be a MINIMAL one --- `exists_isWord`
gives some word, and some word can be arbitrarily long.  Padding a minimal word
by a letter and its inverse costs exactly two. -/
theorem exists_side_spelling_of_alphabet_le {Λ : Type w}
    {D : GGT.RelGenSet G Λ}
    (hle : A.alphabet.carrier ⊆ D.base) (hN : Suitable A.alphabet N)
    {y : G} {n : ℕ} (hy : wordNorm D.alphabet.carrier y ≤ n) :
    ∃ py : List (GGT.RelLetter G Λ), 0 < py.length ∧ py.length ≤ n + 2 ∧
      (∀ x ∈ py, D.IsLetter x) ∧ GGT.RelLetter.listVal py = y ∧
        wordNorm D.alphabet.carrier (GGT.RelLetter.listVal py) ≤ n := by
  obtain ⟨l, hl, hlen⟩ :=
    exists_isWord_length_eq D.alphabet.symmetricGenerating y
  obtain ⟨w, hwlet, hwval, hwlen⟩ :=
    GGT.OsinComponents.exists_relWord D l hl.letters
  obtain ⟨g, hg, hginv⟩ := exists_mem_base_of_base_le hle hN
  have hval : GGT.RelLetter.listVal
      (GGT.RelLetter.base g :: GGT.RelLetter.base g⁻¹ :: w)
      = y := by
    simp only [GGT.RelLetter.listVal, List.map_cons, GGT.RelLetter.val,
      List.prod_cons, mul_inv_cancel_left]
    change GGT.RelLetter.listVal w = y
    rw [hwval, hl.prod_eq]
  refine ⟨GGT.RelLetter.base g :: GGT.RelLetter.base g⁻¹ :: w,
    by simp, ?_, ?_, hval, ?_⟩
  · simp only [List.length_cons, hwlen, hlen]
    omega
  · intro x hx
    rcases List.mem_cons.mp hx with rfl | hx
    · exact hg
    · rcases List.mem_cons.mp hx with rfl | hx
      · exact hginv
      · exact hwlet x hx
  · rwa [hval]

/-- **The two-subgroup core's short sides.**  The form the composition takes
them in, with the base containing Hull's alphabet by
`HullSC.HypEmbeddedCore₂.base_le`. -/
theorem exists_side_spelling₂ (E : HypEmbeddedCore₂ A N)
    (hN : Suitable A.alphabet N) {y : G} {n : ℕ}
    (hy : wordNorm E.rel.alphabet.carrier y ≤ n) :
    ∃ py : List (GGT.RelLetter G Bool), 0 < py.length ∧ py.length ≤ n + 2 ∧
      (∀ x ∈ py, E.rel.IsLetter x) ∧ GGT.RelLetter.listVal py = y ∧
        wordNorm E.rel.alphabet.carrier (GGT.RelLetter.listVal py) ≤ n :=
  exists_side_spelling_of_alphabet_le E.base_le hN hy

end ShortSide

end HullSC
end GroupApproximation
