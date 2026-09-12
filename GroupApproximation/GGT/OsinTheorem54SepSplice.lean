import GroupApproximation.GGT.OsinTheorem54SepGeodesicRuns
import GroupApproximation.GGT.OsinTheorem54SepSubGeodesic
import GroupApproximation.GGT.OsinTheorem54SepSegmentVertex
import GroupApproximation.GGT.DGOCycleSplice

/-!
# Replacing a stretch of a geodesic by another geodesic

If `w` is a geodesic from `f` to `g` and `u` is any geodesic between two of its
vertices, then `w.take k ++ (u ++ w.drop j)` is again a geodesic from `f` to
`g`: the lengths add through the two on-geodesic vertices, and `|u|` is `j - k`
because the stretch of `w` it replaces is itself geodesic.

That is the construction Osin's Lemma 4.9 splices with, and it is what lets
Lemma 5.9 stop asking an arbitrary geodesic to penetrate essentially.  Instead
of demanding essentiality of the component `h48` hands us on the stretch of `w`
--- which is the over-transcription of Definition 4.3's "SOME geodesic" --- the
witness geodesic named by that definition is spliced into `w`, and the component
it already carries travels with its span untouched.

`DGOCycleSplice` supplies the coordinates: `vertex_splice` for the vertices in
the three ranges, `getElem_splice_mid` for the letters of the inserted stretch.
This module adds the one thing that file did not need --- that the result is
geodesic --- and the consequence that makes the transport free: in a geodesic
word an index carrying an `H_λ`-letter IS a component, since components of
geodesics are single letters.
-/

namespace GroupApproximation
namespace GGT
namespace OsinComponents

open GroupApproximation.WordMetric

universe u w

variable {G : Type u} [Group G] {Λ : Type w}

/-- **In a geodesic word, carrying an `H_λ`-letter is being a component.**

The maximality clauses come for free: the run containing the position has
length one, so it starts and ends where the position does. -/
theorem isComp_of_isCompOf_geodesic (D : RelGenSet G Λ) (lam : Λ) {f g : G}
    {ws : List (RelLetter G Λ)} (hw : IsGeodesicWord D f g ws) {i : ℕ}
    (hi : i < ws.length) (hc : (ws[i]'hi).IsCompOf lam) :
    IsComp lam ws i (i + 1) := by
  obtain ⟨a, b, hai, hib, hcomp⟩ := exists_isComp_of_isCompOf lam ws i hi hc
  have hb : b = a + 1 := isComp_eq_succ_of_isGeodesicWord D lam hw hcomp
  have hae : a = i := by omega
  subst hae
  rw [hb] at hcomp
  exact hcomp

/-- **A geodesic with one stretch replaced by another geodesic is geodesic.** -/
theorem isGeodesicWord_splice (D : RelGenSet G Λ) {f g : G}
    {ws us : List (RelLetter G Λ)} (hw : IsGeodesicWord D f g ws) {k j : ℕ}
    (hkj : k ≤ j) (hj : j ≤ ws.length)
    (hu : IsGeodesicWord D (vertex f ws k) (vertex f ws j) us) :
    IsGeodesicWord D f g (ws.take k ++ (us ++ ws.drop j)) := by
  have hvk : f * RelLetter.listVal (ws.take k) = vertex f ws k :=
    (vertex_eq_mul_listVal_take ws f k).symm
  have hvj : f * RelLetter.listVal (ws.take j) = vertex f ws j :=
    (vertex_eq_mul_listVal_take ws f j).symm
  have hsplit : RelLetter.listVal (ws.take j) * RelLetter.listVal (ws.drop j)
      = RelLetter.listVal ws := by
    rw [← listVal_append, List.take_append_drop]
  have hsuf : vertex f ws j * RelLetter.listVal (ws.drop j) = g := by
    rw [← hvj, mul_assoc, hsplit, hw.2.1]
  -- the replaced stretch is geodesic, so `us` has its length
  have hseg := isGeodesicWord_segment D hw hkj hj
  have hlenseg : ((ws.drop k).take (j - k)).length = j - k :=
    length_segment ws k (j - k) (by omega)
  have hdist : wordDist D.alphabet.carrier (vertex f ws k) (vertex f ws j)
      = j - k := by
    rw [← hseg.2.2, hlenseg]
  have hlenu : us.length = j - k := by
    rw [hu.2.2, hdist]
  refine ⟨?_, ?_, ?_⟩
  · intro a ha
    rcases List.mem_append.mp ha with h | h
    · exact hw.1 a (List.take_subset k ws h)
    · rcases List.mem_append.mp h with h' | h'
      · exact hu.1 a h'
      · exact hw.1 a (List.drop_subset j ws h')
  · rw [listVal_append, listVal_append, ← mul_assoc, hvk, ← mul_assoc,
      hu.2.1, hsuf]
  · rw [List.length_append, List.length_append, List.length_take,
      List.length_drop, hlenu, ← hw.2.2]
    omega

end OsinComponents
end GGT
end GroupApproximation
