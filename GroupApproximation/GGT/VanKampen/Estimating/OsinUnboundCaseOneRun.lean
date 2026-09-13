import GroupApproximation.GGT.VanKampen.Estimating.OsinLemma94CaseOneWalk
import GroupApproximation.GGT.VanKampen.Estimating.OsinUnboundCaseOneFace
import GroupApproximation.GGT.VanKampen.Estimating.UnboundNonemptyConnectors
import GroupApproximation.Meta.AxiomGuard

/-!
# Case 1 of Osin's Lemma 9.4 from the face walk

In Case 1 of the proof of Osin's Appendix Lemma 9.4 (arXiv:math/0411039v3), a backwards
connector pair (39) from an (A1) side to an (A1) or (A2) side of a maximal polygon bounds a new
contiguity region, which contradicts the maximality of the selected system.

`osinLemma94CaseOne_false_of_walk` derives the contradiction for one connector pair from the face
walk `OsinLemma94CaseOneWalkStatement`.  The walk reads `X ++ q ++ Y ++ p⁻¹` from some corner of
the polygon face.  The connectors of the pair carry the values of `X` and `Y`, and an empty
connector is spelled by a letter and its inverse (`WordConnectorPair.exists_nonempty_connectors`),
so they have length and norm at most `ε` once `ε ≥ 3`.  The face is no relator cell and lies in no
selected region, so `RealizedSectionFamily.false_of_quadrilateral_face` gives the contradiction.

`osinLemma94CaseOneInput_of_walk` proves `OsinLemma94CaseOneInput` from the walk alone.
`osinLemma94CaseOneInput_of_walk_of_sameCell` takes the pairs whose two sides have the same kind
from the named hypothesis `OsinLemma94CaseOneSameCellStatement`, and uses the walk only for the
pairs whose sides have different kinds.
-/

namespace GroupApproximation.GGT.VanKampen

universe u w v

open GroupApproximation.GGT.VanKampen.Embedded
open GroupApproximation.GGT.VanKampen.UnboundEstimate

/-- **One backwards connector pair of Case 1 from the face walk.**  Once `ε ≥ 3`, a backwards
connector pair of polygon `k` whose target side is not a cutting path gives a contradiction. -/
theorem osinLemma94CaseOne_false_of_walk (hwalk : OsinLemma94CaseOneWalkStatement.{u, w, v})
    {G : Type u} [Group G] {Lambda : Type w} {W : Set (List (RelLetter G Lambda))}
    {D : RelGenSet G Lambda} {lambda c : ℝ} {eps : ℕ} (heps : 3 ≤ eps)
    {Delta : DiscDiagram.{u, w, v} W} {cuts : SectionCuts D lambda c Delta.boundaryWord}
    {S : GloballyDistinguishedSectionFamily D lambda c eps Delta cuts}
    (P : OsinLemma94RealizedPolygons S) (k : Fin P.count)
    (C : WordConnectorPair (symmetricLabelAlphabet D) (P.corner k) (P.word k) (P.sideCount k)
      (P.relatorSides k) (P.longSides k) eps)
    (hback : C.b' < C.b) (hcut : P.kind k C.target ≠ .cutting) : False := by
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

/-- **Case 1 of Lemma 9.4 from the face walk.**  The thresholds are `ε₀ = 3` and `ρ₀ = 1`. -/
theorem osinLemma94CaseOneInput_of_walk (hwalk : OsinLemma94CaseOneWalkStatement.{u, w, v}) :
    OsinLemma94CaseOneInput.{u, w, v} := by
  intro G _ Lambda D _ lambda c mu _ _ _ _ _
  refine ⟨3, fun eps heps => ⟨1, Nat.one_pos, ?_⟩⟩
  intro rho _ W _ Delta cuts _ _ S _ _ P _ k C hback hcut
  exact osinLemma94CaseOne_false_of_walk hwalk heps P k C hback hcut

/-- **Case 1 of Lemma 9.4, with the same-kind pairs as a hypothesis.**  The pairs whose source
and target sides have the same kind come from `OsinLemma94CaseOneSameCellStatement`, and the face
walk handles the other pairs.  The thresholds are `ε₀ = max 3 ε₁` and the `ρ₀` of the hypothesis,
where `ε₁` is the `ε₀` of the hypothesis. -/
theorem osinLemma94CaseOneInput_of_walk_of_sameCell
    (hwalk : OsinLemma94CaseOneWalkStatement.{u, w, v})
    (hsame : OsinLemma94CaseOneSameCellStatement.{u, w, v}) :
    OsinLemma94CaseOneInput.{u, w, v} := by
  intro G _ Lambda D hhyp lambda c mu hlambda hlambda1 hc hmu hmu1
  obtain ⟨eps1, hsame1⟩ := hsame D hhyp lambda c mu hlambda hlambda1 hc hmu hmu1
  refine ⟨max 3 eps1, fun eps heps => ?_⟩
  obtain ⟨rho0, hrho0, hsame2⟩ := hsame1 eps ((le_max_right 3 eps1).trans heps)
  refine ⟨rho0, hrho0, ?_⟩
  intro rho hrho W hW Delta cuts hleast hpos S hcard hmin P hmax k C hback hcut
  by_cases hkind : P.kind k C.source = P.kind k C.target
  · exact hsame2 rho hrho W hW Delta cuts hleast hpos S hcard hmin P hmax k C hback hcut hkind
  · exact osinLemma94CaseOne_false_of_walk hwalk ((le_max_left 3 eps1).trans heps) P k C hback
      hcut

end GroupApproximation.GGT.VanKampen

#audit_axioms GroupApproximation.GGT.VanKampen.osinLemma94CaseOne_false_of_walk
#audit_axioms GroupApproximation.GGT.VanKampen.osinLemma94CaseOneInput_of_walk
#audit_axioms GroupApproximation.GGT.VanKampen.osinLemma94CaseOneInput_of_walk_of_sameCell
