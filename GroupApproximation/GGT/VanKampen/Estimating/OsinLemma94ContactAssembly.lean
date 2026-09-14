import GroupApproximation.GGT.VanKampen.Estimating.OsinLemma94ContactWords
import GroupApproximation.GGT.VanKampen.Estimating.OsinLemma94ContactMapCounts
import GroupApproximation.Meta.AxiomGuard

/-!
# Osin's Lemma 9.4: the contact transitions from three pieces

The contact transitions of the polygons with an (A1) side are the object changes and the section
corners (`card_contactTransitions_le`).  A polygon with at most one neighbour has no object change,
and a rich polygon has at most `2 d_k` of them (`OsinLemma94ObjectChangesStatement`).  So the object
changes number at most `2 ∑_{k rich} d_k`.

The contact map has at least `2 ∑ d_k` darts and at most `#rich + n + 1` vertices, all its faces
have degree at least four, and it is a restriction of the planar dual.  The small-face budget gives
`2 ∑ d_k + 6 ≤ 3 (#rich + n + 1) + t`, and `2 #rich ≤ ∑ d_k`, so `∑ d_k ≤ 6 n + 2 t`.  With
`t ≤ K₂ n` (`OsinLemma94ContactMapSmallFacesInput`) and the section corners `≤ K₁ n`
(`OsinLemma94SectionCornersInput`), the contact transitions number at most `(12 + 4 K₂ + K₁) n`.

* `sum_card_objectChanges_le`: the object changes over the polygons with an (A1) side.
* `richNeighbourSum_le`: the Euler count on the contact map.
* `osinLemma94ContactTransitionInput_of_pieces`: `OsinLemma94ContactTransitionInput` from the
  object change bound, the section corners and the small faces.

## Manuscript status

Infrastructure for `thm:hull` (through the contact count of Osin's Lemma 9.4,
arXiv:math/0411039v3, §9); certifies no printed sentence on its own.  The theorem is a reduction
over three named pieces.
-/

namespace GroupApproximation.GGT.VanKampen

universe u w v

open GroupApproximation.GGT.VanKampen.Embedded
open scoped Classical

namespace OsinLemma94RealizedPolygons

variable {G : Type u} [Group G] {Lambda : Type w} {W : Set (List (RelLetter G Lambda))}
  {D : RelGenSet G Lambda} {lambda c : ℝ} {eps : ℕ} {Delta : DiscDiagram.{u, w, v} W}
  {cuts : SectionCuts D lambda c Delta.boundaryWord}
  {S : GloballyDistinguishedSectionFamily D lambda c eps Delta cuts}

/-- **The object changes over the polygons with an (A1) side** number at most `2 ∑_{k rich} d_k`. -/
theorem sum_card_objectChanges_le (hobj : OsinLemma94ObjectChangesStatement.{u, w, v})
    (P : OsinLemma94RealizedPolygons S) :
    ∑ k ∈ P.relatorPolygons, (P.objectChanges k).card ≤ 2 * P.richNeighbourSum := by
  calc ∑ k ∈ P.relatorPolygons, (P.objectChanges k).card
      ≤ ∑ k ∈ Finset.univ, (P.objectChanges k).card :=
        Finset.sum_le_sum_of_subset (Finset.subset_univ _)
    _ = ∑ k ∈ P.richPolygons, (P.objectChanges k).card := by
        refine (Finset.sum_subset (Finset.subset_univ _) fun k _ hk => ?_).symm
        have hnot : ¬ P.Rich k := fun h => hk (by simpa [richPolygons] using h)
        have hle : (P.neighbours k).card ≤ 1 := by
          unfold Rich at hnot
          omega
        rw [P.objectChanges_eq_empty_of_card_le_one k hle, Finset.card_empty]
    _ ≤ ∑ k ∈ P.richPolygons, 2 * (P.neighbours k).card :=
        Finset.sum_le_sum fun k hk => hobj S P k (by simpa [richPolygons] using hk)
    _ = 2 * P.richNeighbourSum := by
        rw [richNeighbourSum, Finset.mul_sum]

/-- **The Euler count on the contact map**: `∑_{k rich} d_k ≤ 6 n + 2 t`. -/
theorem richNeighbourSum_le (P : OsinLemma94RealizedPolygons S) :
    P.richNeighbourSum ≤ 6 * S.diagram.rCellCount +
      2 * (Finset.univ.filter fun f : P.contactMap.Face => P.contactMap.faceDegree f < 6).card := by
  have hdarts := P.two_mul_richNeighbourSum_le_dartCount
  by_cases hne : Nonempty P.contactMap.Dart
  · have hbudget := CombMap.two_mul_edgeCount_add_six_le_of_isRestriction
      (dual_planar_diagram S) P.contactMap_isRestriction hne P.four_le_faceDegree_contactMap
    have hE := P.contactMap.dartCount_eq_two_mul_edgeCount
    have hV := P.vertexCount_contactMap_le
    have hR := P.two_mul_card_richPolygons_le
    omega
  · have h0 : P.contactMap.dartCount = 0 := by
      unfold CombMap.dartCount
      haveI : IsEmpty P.contactMap.Dart := not_nonempty_iff.mp hne
      exact Nat.card_of_isEmpty
    omega

end OsinLemma94RealizedPolygons

/-- **The contact transitions of Lemma 9.4 from three pieces**, with constant `12 + 4 K₂ + K₁`. -/
theorem osinLemma94ContactTransitionInput_of_pieces
    (hobj : OsinLemma94ObjectChangesStatement.{u, w, v})
    (hsec : OsinLemma94SectionCornersInput.{u, w, v})
    (hsmall : OsinLemma94ContactMapSmallFacesInput.{u, w, v}) :
    OsinLemma94ContactTransitionInput.{u, w, v} := by
  intro G _ Lambda D hhyper lambda c mu hlambda hlambda1 hc hmu hmu16
  obtain ⟨e1, h1⟩ := hsec D hhyper lambda c mu hlambda hlambda1 hc hmu hmu16
  obtain ⟨e2, h2⟩ := hsmall D hhyper lambda c mu hlambda hlambda1 hc hmu hmu16
  refine ⟨max e1 e2, fun eps heps => ?_⟩
  obtain ⟨K1, r1, hr1, hK1⟩ := h1 eps ((le_max_left _ _).trans heps)
  obtain ⟨K2, r2, _, hK2⟩ := h2 eps ((le_max_right _ _).trans heps)
  refine ⟨12 + 4 * K2 + K1, max r1 r2, lt_of_lt_of_le hr1 (le_max_left _ _),
    fun rho hrho W hW Delta cuts hleast hcells hbelow S hcard hminimal P hmax => ?_⟩
  have hsecb := hK1 rho ((le_max_left _ _).trans hrho) W hW Delta cuts hleast hcells hbelow S hcard
    hminimal P hmax
  have hsmallb := hK2 rho ((le_max_right _ _).trans hrho) W hW Delta cuts hleast hcells hbelow S
    hcard hminimal P hmax
  have hn : S.diagram.rCellCount = Delta.rCellCount := S.equiv.rCellCount_eq
  have hobjb := P.sum_card_objectChanges_le hobj
  have hsum := P.richNeighbourSum_le
  rw [hn] at hsum
  have hsplit : ∑ k ∈ P.relatorPolygons, (P.contactTransitions k).card ≤
      ∑ k ∈ P.relatorPolygons, (P.objectChanges k).card +
        ∑ k ∈ P.relatorPolygons, (P.sectionCorners k).card := by
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_le_sum fun k _ => P.card_contactTransitions_le k
  have e : (12 + 4 * K2 + K1) * Delta.rCellCount =
      12 * Delta.rCellCount + 4 * (K2 * Delta.rCellCount) + K1 * Delta.rCellCount := by ring
  rw [e]
  omega

end GroupApproximation.GGT.VanKampen

#audit_axioms GroupApproximation.GGT.VanKampen.OsinLemma94RealizedPolygons.sum_card_objectChanges_le
#audit_axioms GroupApproximation.GGT.VanKampen.OsinLemma94RealizedPolygons.richNeighbourSum_le
#audit_axioms GroupApproximation.GGT.VanKampen.osinLemma94ContactTransitionInput_of_pieces
