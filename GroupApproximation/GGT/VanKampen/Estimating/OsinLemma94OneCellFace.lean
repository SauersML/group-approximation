import GroupApproximation.GGT.VanKampen.Estimating.OsinLemma94CaseOneWalkHolds
import GroupApproximation.GGT.VanKampen.Estimating.OsinLemma94OneCellMorse
import GroupApproximation.GGT.VanKampen.SymmetricLabelAlphabet
import GroupApproximation.Meta.AxiomGuard

/-!
# The one-cell Morse kill on the face walk of Lemma 9.4, Case 1

Osin (math/0411039v3, §9), Lemma 9.4, Case 1, when the source and target sides of a backwards
connector pair lie across one relator cell `Π`.  `OsinLemma94OneCellMorse` kills a pocket with no
relator cell from metric data on the face walk.  This file reads that data off the polygon and the
connector pair.

* `CaseOneWalk.polygon_segment_value`: a window `[a, a']` of a side carries the value from the
  corner at `a` to the corner at `a'`.
* `osinLemma94CaseOneWalk_sameCell`: when the two sides have one kind, both are arcs of one relator
  cell `j`, and some rotation of the face walk reads `X ++ q⁻¹ ++ Y ++ p⁻¹` with `p`, `q` nonempty
  arcs of cell `j`.  The reversed arcs carry the values of the source segment `[a, a']` and the
  target segment `[b', b]`.  `OsinLemma94CaseOneWalkStatement` records neither these values nor
  that the target cell is the source cell.
* `CaseOneWalk.wordNorm_lt_of_start_connector` and `_end_connector`: an element carrying one
  corner of a connector to the other has word norm less than `ε`.
* `CaseOneWalk.lt_wordNorm_of_source_segment` and `_target_segment`: the inverse of an element
  carrying one end of a segment to the other has word norm more than `ε`.
* `false_of_cellFree_pocket_face_X_morse` and `_Y_morse`: the two Morse kills over the polygon, the
  connector pair and the walk of `osinLemma94CaseOneWalk_sameCell`.

## Manuscript status

Infrastructure for `thm:hull` (tex 1636, "Hull's small cancellation theorem", through Osin's
Lemma 4.4); certifies no printed sentence on its own.
-/

namespace GroupApproximation.GGT.VanKampen

universe u w v

open GroupApproximation.GGT.VanKampen.Embedded
open GroupApproximation.GGT.VanKampen.UnboundEstimate
open GroupApproximation.GGT.OsinComponents

namespace CaseOneWalk

section Diagram

variable {G : Type u} [Group G] {Lambda : Type w} {W : Set (List (RelLetter G Lambda))}
  {Delta : DiscDiagram.{u, w, v} W}

/-- A reversed arc reads the inverse of what the arc reads. -/
theorem listVal_dartWord_reverseDarts_inv {cycle : List Delta.toCombMap.Dart}
    (arc : CyclicArc cycle) :
    (RelLetter.listVal (dartWord Delta arc.reverseDarts))⁻¹ =
      RelLetter.listVal (dartWord Delta arc.darts) := by
  have e : arc.reverseDarts = Embedded.invDarts Delta arc.darts := rfl
  rw [e, Embedded.listVal_dartWord_invDarts, inv_inv]

end Diagram

section Polygons

variable {G : Type u} [Group G] {Lambda : Type w} {W : Set (List (RelLetter G Lambda))}
  {D : RelGenSet G Lambda} {lambda c : ℝ} {eps : ℕ} {Delta : DiscDiagram.{u, w, v} W}
  {cuts : SectionCuts D lambda c Delta.boundaryWord}
  {S : GloballyDistinguishedSectionFamily D lambda c eps Delta cuts}

/-- A window `[a, a']` of side `i` carries the value from the corner at `a` to the corner
at `a'`. -/
theorem polygon_segment_value (P : OsinLemma94RealizedPolygons S) (k : Fin P.count) (i : ℕ)
    {a a' : ℕ} (h : a ≤ a') :
    vertex (P.corner k i) (P.word k i) a *
        RelLetter.listVal (dartWord S.diagram (((P.sideDarts k i).drop a).take (a' - a))) =
      vertex (P.corner k i) (P.word k i) a' := by
  have hw : ∀ t, (P.word k i).take t = dartWord S.diagram ((P.sideDarts k i).take t) := by
    intro t
    simp only [OsinLemma94RealizedPolygons.word, dartWord, List.map_take]
  rw [OsinComponents.vertex_eq_mul_listVal_take, OsinComponents.vertex_eq_mul_listVal_take, hw,
    hw, mul_assoc, walkValue_take_window (P.sideDarts k i) h]

/-- The face walk of polygon `k`, rotated to its base, has value `1`. -/
theorem polygon_face_value (P : OsinLemma94RealizedPolygons S) (k : Fin P.count) :
    RelLetter.listVal (dartWord S.diagram
      ((S.diagram.faceBoundary (P.face k)).darts.rotate (P.base k))) = 1 := by
  rw [P.walk k]
  exact polygon_walk_value P k

/-- A rotation of the face walk that reads two reversed arcs, as a rotation of the walk at its
base. -/
theorem polygon_face_isRotated (P : OsinLemma94RealizedPolygons S) (k : Fin P.count)
    {cycle : List S.diagram.toCombMap.Dart} {p q : CyclicArc cycle}
    {X Y : List S.diagram.toCombMap.Dart} {r : ℕ}
    (htrav : (S.diagram.faceBoundary (P.face k)).darts.rotate r =
      X ++ q.reverseDarts ++ Y ++ p.reverseDarts) :
    (S.diagram.faceBoundary (P.face k)).darts.rotate (P.base k) ~r
      X ++ Embedded.invDarts S.diagram q.darts ++ Y ++ Embedded.invDarts S.diagram p.darts :=
  (List.IsRotated.forall (S.diagram.faceBoundary (P.face k)).darts (P.base k)).trans ⟨r, htrav⟩

end Polygons

section Connectors

variable {G : Type u} [Group G] {Lambda : Type w} {D : RelGenSet G Lambda} {v : ℕ → G}
  {word : ℕ → List (RelLetter G Lambda)} {n eps : ℕ} {A B : Set ℕ}

/-- If `g` carries the corner at `b` to the corner at `a`, then `g` is the value of the start
connector, so its word norm is less than `ε`. -/
theorem wordNorm_lt_of_start_connector
    (C : WordConnectorPair (symmetricLabelAlphabet D) v word n A B eps) {g : G}
    (hg : vertex (v C.target) (word C.target) C.b * g =
      vertex (v C.source) (word C.source) C.a) :
    WordMetric.wordNorm D.alphabet.carrier g < eps := by
  obtain ⟨-, -, hlen⟩ := C.start_geodesic
  rw [eq_inv_mul_of_mul_eq hg, ← symmetricLabelAlphabet.wordNorm_eq D]
  have h := C.start_short
  rw [hlen] at h
  exact h

/-- If `g` carries the corner at `a'` to the corner at `b'`, then `g` is the value of the end
connector, so its word norm is less than `ε`. -/
theorem wordNorm_lt_of_end_connector
    (C : WordConnectorPair (symmetricLabelAlphabet D) v word n A B eps) {g : G}
    (hg : vertex (v C.source) (word C.source) C.a' * g =
      vertex (v C.target) (word C.target) C.b') :
    WordMetric.wordNorm D.alphabet.carrier g < eps := by
  obtain ⟨-, -, hlen⟩ := C.end_geodesic
  rw [eq_inv_mul_of_mul_eq hg, ← symmetricLabelAlphabet.wordNorm_eq D]
  have h := C.end_short
  rw [hlen] at h
  exact h

/-- If `g` carries the corner at `a` to the corner at `a'`, then `g⁻¹` has word norm more than `ε`:
the source segment is long. -/
theorem lt_wordNorm_of_source_segment
    (C : WordConnectorPair (symmetricLabelAlphabet D) v word n A B eps) {g : G}
    (hg : vertex (v C.source) (word C.source) C.a * g =
      vertex (v C.source) (word C.source) C.a') :
    eps < WordMetric.wordNorm D.alphabet.carrier g⁻¹ := by
  rw [WordMetric.wordNorm_inv D.alphabet.symmetricGenerating, eq_inv_mul_of_mul_eq hg,
    ← symmetricLabelAlphabet.wordNorm_eq D]
  exact C.source_long

/-- If `g` carries the corner at `b'` to the corner at `b`, then `g⁻¹` has word norm more than `ε`:
the target segment is long. -/
theorem lt_wordNorm_of_target_segment
    (C : WordConnectorPair (symmetricLabelAlphabet D) v word n A B eps) {g : G}
    (hg : vertex (v C.target) (word C.target) C.b' * g =
      vertex (v C.target) (word C.target) C.b) :
    eps < WordMetric.wordNorm D.alphabet.carrier g⁻¹ := by
  rw [eq_inv_mul_of_mul_eq hg, mul_inv_rev, inv_inv, ← symmetricLabelAlphabet.wordNorm_eq D]
  exact C.target_long

end Connectors

end CaseOneWalk

open CaseOneWalk

/-- **The face walk around a backwards connector pair on one relator cell.**  When the source and
target sides of a backwards connector pair of polygon `k` have one kind, both lie across one
relator cell `j`, and some rotation of the face walk reads `X ++ q⁻¹ ++ Y ++ p⁻¹` with `p` and `q`
nonempty arcs of cell `j`.  The reversed arcs `p⁻¹` and `q⁻¹` carry the values of the source
segment `[a, a']` and the target segment `[b', b]`, and `X`, `Y` join the corners of the two
segments with the values of the corners they join. -/
theorem osinLemma94CaseOneWalk_sameCell {G : Type u} [Group G] {Lambda : Type w}
    {W : Set (List (RelLetter G Lambda))} {D E : RelGenSet G Lambda} {lambda c : ℝ} {eps : ℕ}
    {Delta : DiscDiagram.{u, w, v} W} {cuts : SectionCuts D lambda c Delta.boundaryWord}
    {S : GloballyDistinguishedSectionFamily D lambda c eps Delta cuts}
    (P : OsinLemma94RealizedPolygons S) (k : Fin P.count)
    (C : WordConnectorPair E (P.corner k) (P.word k) (P.sideCount k) (P.relatorSides k)
      (P.longSides k) eps)
    (hback : C.b' < C.b) (hkind : P.kind k C.source = P.kind k C.target) :
    ∃ (j : Fin S.diagram.rCellCount) (sourceArc targetArc : CyclicArc (cellDarts S.diagram j))
      (X Y : List S.diagram.toCombMap.Dart) (r : ℕ),
      P.kind k C.source = .cell j ∧
        (S.diagram.faceBoundary (P.face k)).darts.rotate r =
          X ++ targetArc.reverseDarts ++ Y ++ sourceArc.reverseDarts ∧
        0 < sourceArc.length ∧ 0 < targetArc.length ∧
        vertex (P.corner k C.source) (P.word k C.source) C.a *
            RelLetter.listVal (dartWord S.diagram sourceArc.reverseDarts) =
          vertex (P.corner k C.source) (P.word k C.source) C.a' ∧
        vertex (P.corner k C.target) (P.word k C.target) C.b' *
            RelLetter.listVal (dartWord S.diagram targetArc.reverseDarts) =
          vertex (P.corner k C.target) (P.word k C.target) C.b ∧
        vertex (P.corner k C.source) (P.word k C.source) C.a' *
            RelLetter.listVal (dartWord S.diagram X) =
          vertex (P.corner k C.target) (P.word k C.target) C.b' ∧
        vertex (P.corner k C.target) (P.word k C.target) C.b *
            RelLetter.listVal (dartWord S.diagram Y) =
          vertex (P.corner k C.source) (P.word k C.source) C.a := by
  obtain ⟨j, hj⟩ : ∃ j, P.kind k C.source = .cell j := C.source_mem
  have hs := C.source_lt
  have ht := C.target_lt
  have hfwd := C.source_forward
  have ha' : C.a' ≤ (P.sideDarts k C.source).length :=
    C.a'_le.trans_eq (polygon_length_word P k _)
  have hb : C.b ≤ (P.sideDarts k C.target).length :=
    C.b_le.trans_eq (polygon_length_word P k _)
  obtain ⟨X, Y, r, hrot, hX, hY⟩ :=
    polygon_four_windows P k hs ht C.distinct (le_of_lt hfwd) ha' (le_of_lt hback) hb
  have hsv := polygon_segment_value P k C.source (le_of_lt hfwd)
  have htv := polygon_segment_value P k C.target (le_of_lt hback)
  obtain ⟨sarc, hsarc⟩ := P.cell_arc k C.source j hs hj
  obtain ⟨tarc, htarc⟩ := P.cell_arc k C.target j ht (hkind.symm.trans hj)
  have hsl : (P.sideDarts k C.source).length = sarc.length := by
    rw [hsarc, cyclicArc_length_reverseDarts]
  have htl : (P.sideDarts k C.target).length = tarc.length := by
    rw [htarc, cyclicArc_length_reverseDarts]
  obtain ⟨sarc', hslen, hsdarts⟩ :=
    cyclicArc_exists_sub_reverse sarc C.a (C.a' - C.a) (by omega)
  obtain ⟨tarc', htlen, htdarts⟩ :=
    cyclicArc_exists_sub_reverse tarc C.b' (C.b - C.b') (by omega)
  rw [hsarc, ← hsdarts, htarc, ← htdarts] at hrot
  rw [hsarc, ← hsdarts] at hsv
  rw [htarc, ← htdarts] at htv
  refine ⟨j, sarc', tarc', X, Y, r, hj, hrot, ?_, ?_, hsv, htv, hX, hY⟩
  · rw [hslen]
    omega
  · rw [htlen]
    omega

/-- **The Morse kill on the face walk, pocket across `X`.**  `htrav`, `hsource`, `htarget` and `hY`
are as in `osinLemma94CaseOneWalk_sameCell`.  If `X M` bounds a pocket with no relator cell and
`T = q M p` is an arc of the cell, then the long segments give `|p|, |q| > ε`, the start connector
gives `|Y| < ε`, and `false_of_cellFree_pocket_X_morse` applies. -/
theorem false_of_cellFree_pocket_face_X_morse {G : Type u} [Group G] {Lambda : Type w}
    {W : Set (List (RelLetter G Lambda))} {D : RelGenSet G Lambda} {eps rho : ℕ}
    {mu lambda c kappa : ℝ} (hW : OsinCCondition D W eps mu lambda c rho) (hlambda : 0 ≤ lambda)
    (hmorse : UnboundEstimate.IsWordMorseRadius D lambda c kappa)
    (hthreshold : 2 * kappa + c ≤ lambda * eps)
    {Delta : DiscDiagram.{u, w, v} W} {cuts : SectionCuts D lambda c Delta.boundaryWord}
    {S : GloballyDistinguishedSectionFamily D lambda c eps Delta cuts}
    (P : OsinLemma94RealizedPolygons S) (k : Fin P.count)
    (C : WordConnectorPair (symmetricLabelAlphabet D) (P.corner k) (P.word k) (P.sideCount k)
      (P.relatorSides k) (P.longSides k) eps)
    {j : Fin S.diagram.rCellCount} (sourceArc targetArc : CyclicArc (cellDarts S.diagram j))
    {X Y : List S.diagram.toCombMap.Dart} {r : ℕ}
    (htrav : (S.diagram.faceBoundary (P.face k)).darts.rotate r =
      X ++ targetArc.reverseDarts ++ Y ++ sourceArc.reverseDarts)
    (hsource : vertex (P.corner k C.source) (P.word k C.source) C.a *
        RelLetter.listVal (dartWord S.diagram sourceArc.reverseDarts) =
      vertex (P.corner k C.source) (P.word k C.source) C.a')
    (htarget : vertex (P.corner k C.target) (P.word k C.target) C.b' *
        RelLetter.listVal (dartWord S.diagram targetArc.reverseDarts) =
      vertex (P.corner k C.target) (P.word k C.target) C.b)
    (hY : vertex (P.corner k C.target) (P.word k C.target) C.b *
        RelLetter.listVal (dartWord S.diagram Y) =
      vertex (P.corner k C.source) (P.word k C.source) C.a)
    (Q : PocketRegion S.diagram) (hcells : ∀ cell ∈ S.diagram.relatorCells, cell.face ∉ Q.faces)
    {M : List S.diagram.toCombMap.Dart} (hpocket : Q.outer.cycle ~r X ++ M)
    (T : CyclicArc (cellDarts S.diagram j))
    (hT : T.darts = targetArc.darts ++ M ++ sourceArc.darts) : False := by
  have hp := lt_wordNorm_of_source_segment C hsource
  have hq := lt_wordNorm_of_target_segment C htarget
  rw [listVal_dartWord_reverseDarts_inv] at hp hq
  exact false_of_cellFree_pocket_X_morse hW hlambda hmorse hthreshold (polygon_face_value P k)
    sourceArc targetArc T (polygon_face_isRotated P k htrav) Q hcells hpocket hT
    (wordNorm_lt_of_start_connector C hY) hp hq

/-- **The Morse kill on the face walk, pocket across `Y`.**  As
`false_of_cellFree_pocket_face_X_morse`, with `Y M` bounding the pocket, `T = p M q`, and the end
connector giving `|X| < ε`. -/
theorem false_of_cellFree_pocket_face_Y_morse {G : Type u} [Group G] {Lambda : Type w}
    {W : Set (List (RelLetter G Lambda))} {D : RelGenSet G Lambda} {eps rho : ℕ}
    {mu lambda c kappa : ℝ} (hW : OsinCCondition D W eps mu lambda c rho) (hlambda : 0 ≤ lambda)
    (hmorse : UnboundEstimate.IsWordMorseRadius D lambda c kappa)
    (hthreshold : 2 * kappa + c ≤ lambda * eps)
    {Delta : DiscDiagram.{u, w, v} W} {cuts : SectionCuts D lambda c Delta.boundaryWord}
    {S : GloballyDistinguishedSectionFamily D lambda c eps Delta cuts}
    (P : OsinLemma94RealizedPolygons S) (k : Fin P.count)
    (C : WordConnectorPair (symmetricLabelAlphabet D) (P.corner k) (P.word k) (P.sideCount k)
      (P.relatorSides k) (P.longSides k) eps)
    {j : Fin S.diagram.rCellCount} (sourceArc targetArc : CyclicArc (cellDarts S.diagram j))
    {X Y : List S.diagram.toCombMap.Dart} {r : ℕ}
    (htrav : (S.diagram.faceBoundary (P.face k)).darts.rotate r =
      X ++ targetArc.reverseDarts ++ Y ++ sourceArc.reverseDarts)
    (hsource : vertex (P.corner k C.source) (P.word k C.source) C.a *
        RelLetter.listVal (dartWord S.diagram sourceArc.reverseDarts) =
      vertex (P.corner k C.source) (P.word k C.source) C.a')
    (htarget : vertex (P.corner k C.target) (P.word k C.target) C.b' *
        RelLetter.listVal (dartWord S.diagram targetArc.reverseDarts) =
      vertex (P.corner k C.target) (P.word k C.target) C.b)
    (hX : vertex (P.corner k C.source) (P.word k C.source) C.a' *
        RelLetter.listVal (dartWord S.diagram X) =
      vertex (P.corner k C.target) (P.word k C.target) C.b')
    (Q : PocketRegion S.diagram) (hcells : ∀ cell ∈ S.diagram.relatorCells, cell.face ∉ Q.faces)
    {M : List S.diagram.toCombMap.Dart} (hpocket : Q.outer.cycle ~r Y ++ M)
    (T : CyclicArc (cellDarts S.diagram j))
    (hT : T.darts = sourceArc.darts ++ M ++ targetArc.darts) : False := by
  have hp := lt_wordNorm_of_source_segment C hsource
  have hq := lt_wordNorm_of_target_segment C htarget
  rw [listVal_dartWord_reverseDarts_inv] at hp hq
  exact false_of_cellFree_pocket_Y_morse hW hlambda hmorse hthreshold (polygon_face_value P k)
    sourceArc targetArc T (polygon_face_isRotated P k htrav) Q hcells hpocket hT
    (wordNorm_lt_of_end_connector C hX) hp hq

end GroupApproximation.GGT.VanKampen

#audit_axioms GroupApproximation.GGT.VanKampen.CaseOneWalk.polygon_segment_value
#audit_axioms GroupApproximation.GGT.VanKampen.CaseOneWalk.polygon_face_isRotated
#audit_axioms GroupApproximation.GGT.VanKampen.CaseOneWalk.lt_wordNorm_of_source_segment
#audit_axioms GroupApproximation.GGT.VanKampen.CaseOneWalk.lt_wordNorm_of_target_segment
#audit_axioms GroupApproximation.GGT.VanKampen.osinLemma94CaseOneWalk_sameCell
#audit_axioms GroupApproximation.GGT.VanKampen.false_of_cellFree_pocket_face_X_morse
#audit_axioms GroupApproximation.GGT.VanKampen.false_of_cellFree_pocket_face_Y_morse
