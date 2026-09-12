import GroupApproximation.GGT.OsinGeodesicWord
import GroupApproximation.GGT.OsinTheorem54SepSubGeodesic
import GroupApproximation.GGT.HullSCRelatorAdmissible
import GroupApproximation.Meta.AxiomGuard

/-!
# Oriented word segments and short prefix connectors

The metric output of the unbound-polygon argument is indexed by vertices of
original words. These lemmas turn the indices into actual relative words,
including a backwards target segment. Short connectors are constructed by
the geodesic-word existence theorem. The final lemma proves the strict word
length decrease used in Osin's cutting-path argument; embedding the new path
in an O-equivalent diagram is a separate topological step.
-/

namespace GroupApproximation.GGT.VanKampen

open GroupApproximation.WordMetric GroupApproximation.HullSC OsinComponents

universe u w
variable {G : Type u} [Group G] {Lambda : Type w}

/-- The original segment read from index `i` to index `j`, in either direction. -/
def orientedWordSegment (word : List (RelLetter G Lambda)) (i j : ℕ) :
    List (RelLetter G Lambda) :=
  if i ≤ j then (word.drop i).take (j - i)
  else RelWord.revInv ((word.drop j).take (i - j))

theorem orientedWordSegment_transport (word : List (RelLetter G Lambda))
    (v : G) (i j : ℕ) :
    vertex v word i * RelLetter.listVal (orientedWordSegment word i j) =
      vertex v word j := by
  unfold orientedWordSegment
  split_ifs with hij
  · exact listVal_segment word v hij
  · rw [RelWord.listVal_revInv, ← listVal_segment word v (show j ≤ i by omega)]
    group

theorem orientedWordSegment_length (word : List (RelLetter G Lambda))
    {i j : ℕ} (hi : i ≤ word.length) (hj : j ≤ word.length) :
    (orientedWordSegment word i j).length = max i j - min i j := by
  unfold orientedWordSegment
  split_ifs with hij
  · rw [List.length_take, List.length_drop]
    omega
  · rw [RelWord.length_revInv, List.length_take, List.length_drop]
    omega

theorem orientedWordSegment_admissible {D : RelGenSet G Lambda}
    (hsymm : ∀ x ∈ D.base, x⁻¹ ∈ D.base)
    {word : List (RelLetter G Lambda)} (hword : RelWord.IsAdmissible D word)
    (i j : ℕ) : RelWord.IsAdmissible D (orientedWordSegment word i j) := by
  have hpart (k l : ℕ) : RelWord.IsAdmissible D ((word.drop k).take l) :=
    fun a ha => hword a (List.drop_subset k word (List.take_subset l _ ha))
  unfold orientedWordSegment
  split_ifs
  · exact hpart _ _
  · exact isAdmissible_revInv hsymm (hpart _ _)

theorem wordDist_le_orientedWordSegment_length {D : RelGenSet G Lambda}
    (hsymm : ∀ x ∈ D.base, x⁻¹ ∈ D.base)
    {word : List (RelLetter G Lambda)} (hword : RelWord.IsAdmissible D word)
    (v : G) (i j : ℕ) :
    wordDist D.alphabet.carrier (vertex v word i) (vertex v word j) ≤
      (orientedWordSegment word i j).length := by
  have htransport := orientedWordSegment_transport word v i j
  have hval : (vertex v word i)⁻¹ * vertex v word j =
      RelLetter.listVal (orientedWordSegment word i j) := by
    rw [← htransport]
    group
  rw [wordDist, hval]
  exact wordNorm_listVal_le D _ (orientedWordSegment_admissible hsymm hword i j)

/-- A short connector leaving the beginning of a long original subsegment
produces a strictly shorter word from the original basepoint. The connector
and its exact endpoint equation are produced, not assumed. -/
theorem exists_shorter_prefix_connector (D : RelGenSet G Lambda)
    {word : List (RelLetter G Lambda)} (hword : RelWord.IsAdmissible D word)
    (v z : G) {i j eps : ℕ} (hij : i ≤ j) (hj : j ≤ word.length)
    (hlong : eps < wordDist D.alphabet.carrier (vertex v word i) (vertex v word j))
    (hclose : wordDist D.alphabet.carrier (vertex v word i) z < eps) :
    ∃ s : List (RelLetter G Lambda),
      IsGeodesicWord D (vertex v word i) z s ∧ s.length < eps ∧
      RelWord.IsAdmissible D (word.take i ++ s) ∧
      v * RelLetter.listVal (word.take i ++ s) = z ∧
      (word.take i ++ s).length < word.length := by
  obtain ⟨s, hs⟩ := existsGeodesicWord D (vertex v word i) z
  have hslen : s.length < eps := by simpa only [hs.2.2] using hclose
  have hdist := wordDist_vertex_le' D hword v hij hj
  refine ⟨s, hs, hslen, ?_, ?_, ?_⟩
  · intro a ha
    rcases List.mem_append.mp ha with ha | ha
    · exact hword a (List.take_subset i word ha)
    · exact hs.1 a ha
  · rw [RelWord.listVal_append, ← mul_assoc, ← vertex_eq_mul_listVal_take]
    exact hs.2.1
  · rw [List.length_append, List.length_take]
    omega

end GroupApproximation.GGT.VanKampen

#audit_axioms GroupApproximation.GGT.VanKampen.orientedWordSegment_transport
#audit_axioms GroupApproximation.GGT.VanKampen.orientedWordSegment_length
#audit_axioms GroupApproximation.GGT.VanKampen.orientedWordSegment_admissible
#audit_axioms GroupApproximation.GGT.VanKampen.wordDist_le_orientedWordSegment_length
#audit_axioms GroupApproximation.GGT.VanKampen.exists_shorter_prefix_connector
