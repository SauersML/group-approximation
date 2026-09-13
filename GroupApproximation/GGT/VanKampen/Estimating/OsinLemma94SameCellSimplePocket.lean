import GroupApproximation.GGT.VanKampen.Estimating.OsinLemma94SameCellPocketWalk
import GroupApproximation.GGT.VanKampen.Estimating.OsinLemma94SameCellPocketPinch
import GroupApproximation.GGT.VanKampen.Estimating.OsinLemma94SameCellPocketSides
import GroupApproximation.GGT.VanKampen.Estimating.OsinLemma94OneCellSameCell
import GroupApproximation.GGT.VanKampen.Estimating.OsinLemma94OneCellValue
import GroupApproximation.GGT.VanKampen.Estimating.OsinPocketRegionSimpleWalk
import GroupApproximation.GGT.VanKampen.NoncrossingClosedWalkSides
import GroupApproximation.GGT.VanKampen.SurgeryGeodesicCollarStripStep
import GroupApproximation.Meta.AxiomGuard

/-!
# The X-pocket of Lemma 9.4, Case 1, across one relator cell, with a simple walk

Osin (math/0411039v3, §9), Lemma 9.4, Case 1, for a backwards connector pair whose source and
target sides lie across one relator cell `Π` (`OsinLemma94CaseOneSameCellStatement`).  Some
rotation of the face walk reads `X q⁻¹ Y p⁻¹`, some rotation of the carrier of `Π` reads `q B p A`,
`X B` reads an element other than `1`, and the exterior face is off the side of the pocket walk
`invDarts X ++ invDarts B`.  This module refutes the case where that walk is simple
(`osinLemma94CaseOneSimplePocket : OsinLemma94CaseOneSimplePocketStatement`).

* `false_of_simpleWalk_of_below`, at walk level: a simple closed walk `s ++ invDarts T` with `T` an
  arc of a relator cell off its side, the exterior off its side, `‖s‖ ≤ ε` and a value other than
  `1`.  Its pocket region (`PocketRegion.ofSimpleClosedWalk`) follows both boundary walks.  With no
  relator cell inside, the outer cycle reads `1` (`PocketRegion.listVal_outer_eq_one`), against the
  value.  With a relator cell inside, the loop cut refutes it below `Δ`
  (`false_of_pocketRegion_of_below`, with the closed collar
  `GeodesicCollar.StripStep.geodesicCollarStatement_holds`).
* `false_of_simplePocket_X`: the pocket walk of the Case 1 pair is closed
  (`SameCellPocketWalk.isClosedDartWalk_X`), `Π` is off its side
  (`SameCellPocketSides.face_not_mem_sideFaces_X`), and the side `invDarts X` has the norm of the
  end connector (`wordNorm_lt_of_end_connector`).

## Manuscript status

Infrastructure for `thm:hull` (tex 2121, Hull's small cancellation theorem, through Osin's
Lemma 9.4, Case 1); certifies no printed sentence on its own.
-/

namespace GroupApproximation.GGT.VanKampen

universe u w v

open GroupApproximation.GGT.VanKampen.Embedded
open GroupApproximation.GGT.VanKampen.UnboundEstimate
open GroupApproximation.GGT.OsinComponents
open GroupApproximation.GGT.VanKampen.SimpleClosedWalkSides
open GroupApproximation.GGT.VanKampen.CaseOneWalk

namespace SameCellSimplePocket

/-- **`ρ` large enough for the width budget**: some `ρ₀` makes `λ⁻¹ (3ε + c) < (μ/2) ρ` for every
`ρ ≥ ρ₀`. -/
theorem exists_rho_large (lambda c : ℝ) {mu : ℝ} (hmu : 0 < mu) (eps : ℕ) :
    ∃ rho0 : ℕ, ∀ rho : ℕ, rho0 ≤ rho →
      lambda⁻¹ * (3 * (eps : ℝ) + c) < mu / 2 * (rho : ℝ) := by
  set K : ℝ := lambda⁻¹ * (3 * (eps : ℝ) + c)
  refine ⟨⌈2 * K / mu⌉₊ + 1, fun rho hrho => ?_⟩
  have hceil : 2 * K / mu ≤ ((⌈2 * K / mu⌉₊ : ℕ) : ℝ) := Nat.le_ceil _
  have hcast : ((⌈2 * K / mu⌉₊ + 1 : ℕ) : ℝ) ≤ (rho : ℝ) := Nat.cast_le.mpr hrho
  have hlt : 2 * K / mu < (rho : ℝ) := by
    have h1 : ((⌈2 * K / mu⌉₊ + 1 : ℕ) : ℝ) = ((⌈2 * K / mu⌉₊ : ℕ) : ℝ) + 1 :=
      Nat.cast_succ _
    linarith
  have hmul : 2 * K < (rho : ℝ) * mu := (div_lt_iff₀ hmu).mp hlt
  have heq : mu / 2 * (rho : ℝ) = (rho : ℝ) * mu / 2 := by ring
  rw [heq]
  linarith

/-- **A simple pocket walk with a value other than `1`, refuted below `Δ`.**  Let `X` be an
O-equivalent copy of `Δ` with letters as labels, and `walk = s ++ invDarts T` a simple closed walk
of `X`, where `T` is an arc of a relator cell `i` off the side of the walk, the exterior face is off
that side, the value of `s` has word norm at most `ε`, and the walk reads an element other than
`1`.  If clause (b) of Lemma 9.7 holds below the number of relator cells of `Δ` and `ρ` meets the
width budget, this is impossible. -/
theorem false_of_simpleWalk_of_below {G : Type u} [Group G] {Lambda : Type w}
    {W : Set (List (RelLetter G Lambda))} {D : RelGenSet G Lambda} {eps rho : ℕ}
    {mu lambda c : ℝ} (hW : OsinCCondition D W eps mu lambda c rho) (hlambda : 0 < lambda)
    (hlambda1 : lambda ≤ 1) (hc : 0 ≤ c) (hmu : 0 < mu) (hmu1 : mu ≤ 1 / 16) (hrho : 0 < rho)
    (hlarge : lambda⁻¹ * (3 * (eps : ℝ) + c) < mu / 2 * (rho : ℝ))
    {Delta X : DiscDiagram.{u, w, v} W} (hleast : Delta.LeastArea)
    (hbelow : ∀ (Xi : DiscDiagram.{u, w, v} W) (cutsXi : SectionCuts D lambda c Xi.boundaryWord),
      Xi.LeastArea → 0 < Xi.rCellCount → Xi.rCellCount < Delta.rCellCount →
        ∃ T : RealizedSectionFamily D lambda c eps Xi cutsXi, OsinLemma97bConclusion mu T)
    (equiv : OEquivalentDiscDiagram Delta X)
    (hlabel : ∀ d, (symmetricLabelAlphabet D).IsLetter (X.label d))
    {walk s : List X.toCombMap.Dart} (hw : IsSimpleClosedWalk X.toCombMap walk)
    (hout : X.outerFace ∉ sideFaces X.toCombMap walk)
    {i : Fin X.rCellCount} (hi : (cell X i).face ∉ sideFaces X.toCombMap walk)
    (T : CyclicArc (cellDarts X i)) (hdecomposition : walk = s ++ invDarts X T.darts)
    (hnorm : WordMetric.wordNorm D.alphabet.carrier (RelLetter.listVal (dartWord X s)) ≤ eps)
    (hval : RelLetter.listVal (dartWord X walk) ≠ 1) : False := by
  have hinv : invDarts X (PocketRegion.ofSimpleClosedWalk hw hout).outer.cycle = walk :=
    PocketRegion.ofSimpleClosedWalk_invDarts_outer hw hout
  by_cases hcells :
      ∀ C ∈ X.relatorCells, C.face ∉ (PocketRegion.ofSimpleClosedWalk hw hout).faces
  · apply hval
    rw [← hinv, listVal_dartWord_invDarts,
      (PocketRegion.ofSimpleClosedWalk hw hout).listVal_outer_eq_one hcells, inv_one]
  · obtain ⟨C₀, hC₀, hCf⟩ : ∃ C ∈ X.relatorCells,
        C.face ∈ (PocketRegion.ofSimpleClosedWalk hw hout).faces := by
      by_contra hno
      exact hcells fun C hC hmem => hno ⟨C, hC, hmem⟩
    exact false_of_pocketRegion_of_below GeodesicCollar.StripStep.geodesicCollarStatement_holds
      hW hlambda hlambda1 hc hmu hmu1 hrho hlarge hleast hbelow equiv hlabel
      (PocketRegion.ofSimpleClosedWalk hw hout)
      (PocketRegion.ofSimpleClosedWalk_followsBoundary hw hout).1
      (PocketRegion.ofSimpleClosedWalk_followsBoundary hw hout).2 hC₀ hCf hi T s
      (hinv.trans hdecomposition) hnorm

/-- **The X-pocket of a Case 1 one-cell pair with a simple walk, refuted.** -/
theorem false_of_simplePocket_X {G : Type u} [Group G] {Lambda : Type w}
    {W : Set (List (RelLetter G Lambda))} {D : RelGenSet G Lambda} {eps rho : ℕ}
    {mu lambda c : ℝ} (hW : OsinCCondition D W eps mu lambda c rho) (hlambda : 0 < lambda)
    (hlambda1 : lambda ≤ 1) (hc : 0 ≤ c) (hmu : 0 < mu) (hmu1 : mu ≤ 1 / 16) (hrho : 0 < rho)
    (hlarge : lambda⁻¹ * (3 * (eps : ℝ) + c) < mu / 2 * (rho : ℝ))
    {Delta : DiscDiagram.{u, w, v} W} {cuts : SectionCuts D lambda c Delta.boundaryWord}
    (hleast : Delta.LeastArea)
    (hbelow : ∀ (Xi : DiscDiagram.{u, w, v} W) (cutsXi : SectionCuts D lambda c Xi.boundaryWord),
      Xi.LeastArea → 0 < Xi.rCellCount → Xi.rCellCount < Delta.rCellCount →
        ∃ T : RealizedSectionFamily D lambda c eps Xi cutsXi, OsinLemma97bConclusion mu T)
    {S : GloballyDistinguishedSectionFamily D lambda c eps Delta cuts}
    (P : OsinLemma94RealizedPolygons S) (k : Fin P.count)
    (C : WordConnectorPair (symmetricLabelAlphabet D) (P.corner k) (P.word k) (P.sideCount k)
      (P.relatorSides k) (P.longSides k) eps)
    {j : Fin S.diagram.rCellCount} (sourceArc targetArc : CyclicArc (cellDarts S.diagram j))
    {X Y : List S.diagram.toCombMap.Dart} {r : ℕ}
    (htrav : (S.diagram.faceBoundary (P.face k)).darts.rotate r =
      X ++ targetArc.reverseDarts ++ Y ++ sourceArc.reverseDarts)
    (hs : 0 < sourceArc.length) (ht : 0 < targetArc.length)
    (hX : vertex (P.corner k C.source) (P.word k C.source) C.a' *
        RelLetter.listVal (dartWord S.diagram X) =
      vertex (P.corner k C.target) (P.word k C.target) C.b')
    {n : ℕ} {B A : List S.diagram.toCombMap.Dart}
    (hPi : (cellDarts S.diagram j).rotate n = targetArc.darts ++ B ++ sourceArc.darts ++ A)
    (hXB : RelLetter.listVal (dartWord S.diagram (X ++ B)) ≠ 1)
    (hout : S.diagram.outerFace ∉ sideFaces S.diagram.toCombMap
      (invDarts S.diagram X ++ invDarts S.diagram B))
    (hshape : PocketWalkSimpleShape S.diagram (invDarts S.diagram X) (invDarts S.diagram B)) :
    False := by
  have happ : ∀ l₁ l₂ : List S.diagram.toCombMap.Dart,
      RelLetter.listVal (dartWord S.diagram (l₁ ++ l₂)) =
        RelLetter.listVal (dartWord S.diagram l₁) * RelLetter.listVal (dartWord S.diagram l₂) := by
    intro l₁ l₂
    simp [Embedded.dartWord, RelLetter.listVal]
  have hne : X ++ B ≠ [] := fun h => hXB (by
    rw [h]
    simp [Embedded.dartWord, RelLetter.listVal])
  obtain ⟨hne', hchain, hcloses⟩ :=
    SameCellPocketWalk.isClosedDartWalk_X sourceArc targetArc htrav hPi hs ht hne
  have hw : IsSimpleClosedWalk S.diagram.toCombMap
      (invDarts S.diagram X ++ invDarts S.diagram B) :=
    ⟨hne', hchain, hcloses, hshape.1, hshape.2⟩
  obtain ⟨Barc, hBarc⟩ : ∃ arc : CyclicArc (cellDarts S.diagram j), arc.darts = B := by
    have hrot : (cellDarts S.diagram j).rotate (n + targetArc.darts.length) =
        B ++ (sourceArc.darts ++ A ++ targetArc.darts) := by
      rw [← List.rotate_rotate, hPi]
      simp only [List.append_assoc]
      rw [List.rotate_append_length_eq]
      simp only [List.append_assoc]
    exact CyclicArc.exists_darts_eq_of_rotate_eq hrot
  have hsides := SameCellPocketSides.face_not_mem_sideFaces_X (P.face_not_cell k j) sourceArc
    targetArc htrav hPi hs hw.isNoncrossingClosedWalk
  have hnorm : WordMetric.wordNorm D.alphabet.carrier
      (RelLetter.listVal (dartWord S.diagram (invDarts S.diagram X))) ≤ eps := by
    rw [listVal_dartWord_invDarts, WordMetric.wordNorm_inv D.alphabet.symmetricGenerating]
    exact (wordNorm_lt_of_end_connector C hX).le
  have hval : RelLetter.listVal
      (dartWord S.diagram (invDarts S.diagram X ++ invDarts S.diagram B)) ≠ 1 := by
    intro h
    apply hXB
    rw [happ, listVal_dartWord_invDarts, listVal_dartWord_invDarts, ← mul_inv_rev,
      inv_eq_one] at h
    rw [happ]
    exact mul_eq_one_comm.mp h
  exact false_of_simpleWalk_of_below hW hlambda hlambda1 hc hmu hmu1 hrho hlarge hleast hbelow
    S.equiv S.label_admissible hw hout hsides.2 Barc (by rw [hBarc]) hnorm hval

end SameCellSimplePocket

open SameCellSimplePocket in
/-- **The X-pocket with a simple walk**, closed. -/
theorem osinLemma94CaseOneSimplePocket : OsinLemma94CaseOneSimplePocketStatement.{u, w, v} := by
  intro G _ Lambda D _hhyper lambda c mu hlambda hlambda1 hc hmu hmu1
  refine ⟨0, fun eps _ => ?_⟩
  obtain ⟨rho1, hrho1⟩ := exists_rho_large lambda c hmu eps
  refine ⟨max 1 rho1, by omega, fun rho hrho => ?_⟩
  intro W hW Delta cuts hleast _hpos hbelow S _hcard _hmin P _hmax k C _hback _hcut _hkind j
    sourceArc targetArc X Y r _hj htrav hs ht _hsource _htarget hX _hY n B A hPi hXB hout hshape
  exact false_of_simplePocket_X hW hlambda hlambda1 hc hmu hmu1 (by omega)
    (hrho1 rho (le_of_max_le_right hrho)) hleast hbelow P k C sourceArc targetArc htrav hs ht hX
    hPi hXB hout hshape

end GroupApproximation.GGT.VanKampen

#audit_axioms GroupApproximation.GGT.VanKampen.SameCellSimplePocket.exists_rho_large
#audit_axioms GroupApproximation.GGT.VanKampen.SameCellSimplePocket.false_of_simpleWalk_of_below
#audit_axioms GroupApproximation.GGT.VanKampen.SameCellSimplePocket.false_of_simplePocket_X
#audit_closed_axioms GroupApproximation.GGT.VanKampen.osinLemma94CaseOneSimplePocket
