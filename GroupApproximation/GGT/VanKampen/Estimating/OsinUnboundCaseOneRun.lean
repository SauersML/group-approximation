import GroupApproximation.GGT.VanKampen.Estimating.OsinLemma94CaseOneWalk
import GroupApproximation.GGT.VanKampen.Estimating.OsinUnboundCaseOneFace
import GroupApproximation.GGT.VanKampen.Estimating.UnboundNonemptyConnectors
import GroupApproximation.Meta.AxiomGuard

/-!
# Case 1 of Osin's Lemma 9.4 from the face walk

In Case 1 of the proof of Osin's Appendix Lemma 9.4 (arXiv:math/0411039v3), a backwards
connector pair (39) from an (A1) side to an (A1) or (A2) side of a maximal polygon bounds a new
contiguity region, which contradicts the maximality of the selected system.

`osinLemma94CaseOneInput_of_walk` proves `OsinLemma94CaseOneInput` from the face walk
`OsinLemma94CaseOneWalkStatement`.  The walk reads `X ++ q ++ Y ++ p⁻¹` from some corner of the
polygon face.  The connectors of the pair carry the values of `X` and `Y`, and an empty
connector is spelled by a letter and its inverse (`WordConnectorPair.exists_nonempty_connectors`),
so they have length and norm at most `ε` once `ε ≥ 3`.  The face is no relator cell and lies in no
selected region, so `RealizedSectionFamily.false_of_quadrilateral_face` gives the contradiction.
-/

namespace GroupApproximation.GGT.VanKampen

universe u w v

open GroupApproximation.GGT.VanKampen.Embedded
open GroupApproximation.GGT.VanKampen.UnboundEstimate

/-- **Case 1 of Lemma 9.4 from the face walk.**  The thresholds are `ε₀ = 3` and `ρ₀ = 1`. -/
theorem osinLemma94CaseOneInput_of_walk (hwalk : OsinLemma94CaseOneWalkStatement.{u, w, v}) :
    OsinLemma94CaseOneInput.{u, w, v} := by
  intro G _ Lambda D _ lambda c mu _ _ _ _ _
  refine ⟨3, fun eps heps => ⟨1, Nat.one_pos, ?_⟩⟩
  intro rho _ W _ Delta cuts _ _ S _ _ P _ k C hback hcut
  obtain ⟨source, target, sourceArc, targetArc, X, Y, r, htrav, hsource, htarget, -, -, hsection,
    hX, hY⟩ := hwalk P k C hback hcut
  have hsymm := symmetricLabelAlphabet.symmetric D
  obtain ⟨N⟩ := C.exists_nonempty_connectors hsymm (by omega)
  have hcells : ∀ cell ∈ S.diagram.relatorCells, cell.face ≠ P.face k := by
    intro cell hcell
    obtain ⟨j, rfl⟩ := List.mem_iff_get.mp hcell
    exact P.face_not_cell k j
  have hval1 : RelLetter.listVal N.endWord = RelLetter.listVal (dartWord S.diagram X) :=
    N.end_value.trans (mul_left_cancel (C.end_geodesic.2.1.trans hX.symm))
  have hval2 : RelLetter.listVal N.startWord = RelLetter.listVal (dartWord S.diagram Y) :=
    N.start_value.trans (mul_left_cancel (C.start_geodesic.2.1.trans hY.symm))
  have hnorm1 : WordMetric.wordNorm D.alphabet.carrier (RelLetter.listVal N.endWord) ≤ eps := by
    obtain ⟨-, hmul, hlen⟩ := C.end_geodesic
    rw [N.end_value, eq_inv_mul_of_mul_eq hmul, ← symmetricLabelAlphabet.wordNorm_eq D]
    have h := le_of_lt C.end_short
    rw [hlen] at h
    exact h
  have hnorm2 : WordMetric.wordNorm D.alphabet.carrier (RelLetter.listVal N.startWord) ≤ eps := by
    obtain ⟨-, hmul, hlen⟩ := C.start_geodesic
    rw [N.start_value, eq_inv_mul_of_mul_eq hmul, ← symmetricLabelAlphabet.wordNorm_eq D]
    have h := le_of_lt C.start_short
    rw [hlen] at h
    exact h
  exact RealizedSectionFamily.false_of_quadrilateral_face S.toRealizedSectionFamily
    S.label_admissible S.weight_maximal (P.face k) (P.face_ne_outer k) hcells
    (P.face_unselected k) source target sourceArc targetArc X Y r htrav hsource htarget hsection
    N.endWord N.startWord N.end_nonempty N.start_nonempty N.end_admissible
    (fun l hl => HullSC.isLetter_relWordInv _ hsymm (N.end_admissible l hl))
    N.start_admissible
    (fun l hl => HullSC.isLetter_relWordInv _ hsymm (N.start_admissible l hl))
    hval1 hval2 (le_of_lt N.end_short) (le_of_lt N.start_short) hnorm1 hnorm2

end GroupApproximation.GGT.VanKampen

#audit_axioms GroupApproximation.GGT.VanKampen.osinLemma94CaseOneInput_of_walk
