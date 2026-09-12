import GroupApproximation.GGT.DGOProposition414SecondSeparationTransport
import GroupApproximation.GGT.DGOIsolatedSingletonLetter

/-!
# Component cosets under reversal and insertion into an auxiliary cycle

Reading a one-edge component backwards changes its starting vertex to its
terminal vertex, which remains in the same peripheral coset. Inserting an
isolated singleton into the final block preserves separation from all other
component starts in that block, even when a cut changes maximal components.
-/

namespace GroupApproximation.GGT.DGOProposition414

open GroupApproximation.GGT.DGOPolygonCut
open GroupApproximation.GGT.OsinComponents

universe u w
variable {G : Type u} [Group G] {Lambda : Type w}

/-- The start of either orientation of a component edge lies in its coset. -/
theorem orientedEdgeIndex_start_mem
    (D : RelGenSet G Lambda) {lam : Lambda} {word : List (RelLetter G Lambda)}
    (v : G) (hletters : ∀ x ∈ word, D.IsLetter x) {cs cf y : ℕ}
    (hcs : cs ≤ word.length)
    (hedge : EdgeBetween cs cf y) (hcomp : IsComp lam word y (y + 1)) :
    (vertex v word y)⁻¹ *
      vertex (vertex v word cs) (orientedSegment word cs cf)
        (orientedEdgeIndex cs cf y) ∈ D.fam lam := by
  unfold EdgeBetween at hedge
  by_cases hor : cs ≤ cf
  · have hcy : cs ≤ y := by omega
    have hyf : y < cf := by omega
    rw [orientedEdgeIndex, if_pos hor,
      vertex_orientedSegment_of_le word v hor (by omega), Nat.add_sub_of_le hcy,
      inv_mul_cancel]
    exact (D.fam lam).one_mem
  · have hfy : cf ≤ y := by omega
    have hyc : y < cs := by omega
    rw [orientedEdgeIndex, if_neg hor,
      vertex_orientedSegment_of_not_le word v hor hcs (by omega),
      show cs - (cs - (y + 1)) = y + 1 by omega]
    exact span_mem_fam_of_isComp D v hletters hcomp

/-- Opponents in the final block cannot connect to an isolated singleton of
that block at a different position. -/
theorem not_connected_auxiliaryCycle_chord_of_isolated
    (D : RelGenSet G Lambda) (v : G) (left arc right chord : List (RelLetter G Lambda))
    {lam : Lambda} {i r : ℕ} (hletters : ∀ x ∈ chord, D.IsLetter x)
    (hcomp : IsComp lam chord i (i + 1))
    (hiso : IsIsolated D.fam lam
      (v * RelLetter.listVal ((revWord left ++ arc) ++ right)) chord i)
    (hr : r < chord.length) (hne : r ≠ i)
    (hop : IsCompStart lam (auxiliaryCycleWord left arc right chord)
      (left.length + arc.length + right.length + r)) :
    ¬ Connected D.fam lam v (auxiliaryCycleWord left arc right chord)
      (left.length + arc.length + right.length + i)
      (left.length + arc.length + right.length + r) := by
  intro hconn
  obtain ⟨endPos, hfull⟩ := hop
  have hcycle := hfull.1.trans_le hfull.2.1
  have hletter := (isCompOf_auxiliaryCycle_chord_iff lam left arc right chord r hr hcycle).mp
    (hfull.2.2.1 _ le_rfl hfull.1 hcycle)
  have hlocal : Connected D.fam lam
      (v * RelLetter.listVal ((revWord left ++ arc) ++ right)) chord i r := by
    change _ ∈ D.fam lam at hconn ⊢
    rwa [vertex_auxiliaryCycle_chord, vertex_auxiliaryCycle_chord] at hconn
  exact hne (eq_of_isolated_singleton_of_connected_letter D hletters hcomp hiso
    hr le_rfl (Nat.le_succ _) hletter hlocal)

end GroupApproximation.GGT.DGOProposition414

#audit_axioms GroupApproximation.GGT.DGOProposition414.orientedEdgeIndex_start_mem
#audit_axioms GroupApproximation.GGT.DGOProposition414.not_connected_auxiliaryCycle_chord_of_isolated
