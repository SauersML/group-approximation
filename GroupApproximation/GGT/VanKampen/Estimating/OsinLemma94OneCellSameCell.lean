import GroupApproximation.GGT.VanKampen.Estimating.OsinLemma94OneCellFace
import GroupApproximation.GGT.VanKampen.Estimating.OsinPocketLoopCut
import GroupApproximation.GGT.VanKampen.Estimating.OsinPocketGlueCellTransport
import GroupApproximation.GGT.VanKampen.Estimating.OsinAppendixO52LeastArea
import GroupApproximation.GGT.VanKampen.Estimating.OsinAppendixSectionMultipleEdge
import GroupApproximation.GGT.VanKampen.Estimating.OsinUnboundCaseOneFace
import GroupApproximation.Meta.AxiomGuard

/-!
# The one-cell pairs of Lemma 9.4, Case 1: the value-one kills and the relator-cell residual

Osin (math/0411039v3, §9), Lemma 9.4, Case 1, for a backwards connector pair whose source and
target sides lie across one relator cell `Π` (`OsinLemma94CaseOneSameCellStatement`).  Some
rotation of the face walk reads `X q⁻¹ Y p⁻¹`, with `p` and `q` nonempty arcs of `Π`
(`osinLemma94CaseOneWalk_sameCell`).  The face walk has no repeated dart, so `p` and `q` share no
dart, and some rotation of `∂Π` reads `q B p A`.  So `X B` and `Y A` are closed walks.

* `CaseOneSameCell.exists_eq_append_four` and `exists_rotate_eq_append_four`: two nonempty arcs of
  a cycle with no common dart are windows `q B p A` of one rotation.
* `CaseOneSameCell.exists_cellDarts_rotate_eq`: the decomposition of `∂Π`.
* `CaseOneSameCell.listVal_arc_eq_of_value_one_X` and `_Y`: if `X B` reads `1`, the arc `q B p`
  reads the value of `Y`; if `Y A` reads `1`, the arc `p A q` reads the value of `X`.
* `false_of_sameCell_value_one_X` and `_Y`: then that arc is a `(λ, c)`-quasi-geodesic hairpin
  with long ends and a value of word norm less than `ε`, against `2κ + c ≤ λ ε`.  No pocket region
  is built, so spurs, pinches and empty pockets do not arise on these branches.
* `OsinLemma94CaseOneRCellStatement` and `osinLemma94CaseOneSameCell_of_rCell`: the remaining
  branch, where neither `X B` nor `Y A` reads `1`, as a named residual.
* `OsinLemma94CaseOnePocketStatement` and `osinLemma94CaseOneRCell_of_pocket`: a pocket region with
  a relator cell in an O-equivalent copy gives the residual, through
  `nonempty_osinLoopCut_of_pocketRegion` and `OsinLoopCut.false_of_below`.

## Manuscript status

Infrastructure for `thm:hull` (tex 1636, "Hull's small cancellation theorem", through Osin's
Lemma 4.4); certifies no printed sentence on its own.
-/

namespace GroupApproximation.GGT.VanKampen

universe u w v

open GroupApproximation.GGT.VanKampen.Embedded
open GroupApproximation.GGT.VanKampen.UnboundEstimate
open GroupApproximation.GGT.OsinComponents

namespace CaseOneSameCell

/-- **Two windows of a list with no common element.**  If the window of length `lp` of the
rotation of `L` by `m` has no element of the prefix of length `lq`, then `L` reads that prefix, a
stretch, the window, and a stretch. -/
theorem exists_eq_append_four {α : Type*} (L : List α) {lq lp m : ℕ}
    (hq : 0 < lq) (hp : 0 < lp) (hm : m < L.length)
    (hdisj : ∀ d ∈ (L.drop m ++ L.take m).take lp, d ∉ L.take lq) :
    ∃ B A : List α, L = L.take lq ++ B ++ (L.drop m ++ L.take m).take lp ++ A := by
  have h0 : 0 < L.length := by omega
  by_cases hmq : m < lq
  · exfalso
    obtain ⟨k, hk⟩ : ∃ k, lp = k + 1 := ⟨lp - 1, by omega⟩
    have hmem : L[m] ∈ (L.drop m ++ L.take m).take lp := by
      rw [hk, List.drop_eq_getElem_cons hm, List.cons_append, List.take_succ_cons]
      exact List.mem_cons.mpr (Or.inl rfl)
    exact hdisj _ hmem (List.mem_take_iff_getElem.mpr ⟨m, Nat.lt_min.mpr ⟨hmq, hm⟩, rfl⟩)
  by_cases hmp : L.length < m + lp
  · exfalso
    have hmem : L[0] ∈ (L.drop m ++ L.take m).take lp := by
      rw [List.take_append]
      refine List.mem_append_right _ (List.mem_take_iff_getElem.mpr ⟨0, ?_, ?_⟩)
      · simp only [List.length_take, List.length_drop, Nat.lt_min]
        omega
      · simp
    exact hdisj _ hmem (List.mem_take_iff_getElem.mpr ⟨0, Nat.lt_min.mpr ⟨hq, h0⟩, rfl⟩)
  refine ⟨(L.drop lq).take (m - lq), L.drop (m + lp), ?_⟩
  have h1 : L.take m = L.take lq ++ (L.drop lq).take (m - lq) := by
    rw [← List.take_add, Nat.add_sub_of_le (show lq ≤ m by omega)]
  have h2 : (L.drop m ++ L.take m).take lp = (L.drop m).take lp :=
    List.take_append_of_le_length (by rw [List.length_drop]; omega)
  rw [h2, ← h1, ← List.take_add, List.take_append_drop]

/-- **Two arcs of a cycle with no common dart are windows of one rotation.**  If `p` and `q` are
nonempty arcs and no dart of `p` lies on `q`, some rotation of the cycle reads `q B p A`. -/
theorem exists_rotate_eq_append_four {Dart : Type*} {cycle : List Dart} (q p : CyclicArc cycle)
    (hq : 0 < q.length) (hp : 0 < p.length) (hdisj : ∀ d ∈ p.darts, d ∉ q.darts) :
    ∃ (n : ℕ) (B A : List Dart), cycle.rotate n = q.darts ++ B ++ p.darts ++ A := by
  have hqs : q.start.1 < cycle.length + 1 := q.start.isLt
  have hpos : 0 < cycle.length := lt_of_lt_of_le hq q.length_le
  have hqL : q.darts = (cycle.rotate q.start.1).take q.length := by
    rw [CyclicArc.darts, q.rotated_eq_rotate]
  have hrot : (cycle.rotate q.start.1).rotate
      ((p.start.1 + (cycle.length - q.start.1)) % cycle.length) = cycle.rotate p.start.1 := by
    have h := List.rotate_mod (cycle.rotate q.start.1) (p.start.1 + (cycle.length - q.start.1))
    rw [List.length_rotate] at h
    rw [h, List.rotate_rotate, show q.start.1 + (p.start.1 + (cycle.length - q.start.1)) =
      p.start.1 + cycle.length by omega, ← List.rotate_mod cycle (p.start.1 + cycle.length),
      Nat.add_mod_right, List.rotate_mod]
  have hmlt : (p.start.1 + (cycle.length - q.start.1)) % cycle.length < cycle.length :=
    Nat.mod_lt _ hpos
  have hmle : (p.start.1 + (cycle.length - q.start.1)) % cycle.length ≤
      (cycle.rotate q.start.1).length := by
    rw [List.length_rotate]
    exact hmlt.le
  have hpL : p.darts = ((cycle.rotate q.start.1).drop
      ((p.start.1 + (cycle.length - q.start.1)) % cycle.length) ++ (cycle.rotate q.start.1).take
      ((p.start.1 + (cycle.length - q.start.1)) % cycle.length)).take p.length := by
    rw [CyclicArc.darts, p.rotated_eq_rotate, ← hrot, List.rotate_eq_drop_append_take hmle]
  have hm : (p.start.1 + (cycle.length - q.start.1)) % cycle.length <
      (cycle.rotate q.start.1).length := by
    rw [List.length_rotate]
    exact hmlt
  obtain ⟨B, A, h⟩ := exists_eq_append_four (cycle.rotate q.start.1)
    (m := (p.start.1 + (cycle.length - q.start.1)) % cycle.length) hq hp hm
    (by rw [← hpL, ← hqL]; exact hdisj)
  exact ⟨q.start.1, B, A, by rw [hqL, hpL]; exact h⟩

/-- **A rotation `q B p A` of a cycle makes `p A q` an arc.** -/
theorem exists_arc_darts_eq_rotate_four {Dart : Type*} {cycle : List Dart} {n : ℕ}
    {q B p A : List Dart} (hPi : cycle.rotate n = q ++ B ++ p ++ A) :
    ∃ T : CyclicArc cycle, T.darts = p ++ A ++ q := by
  have h : cycle.rotate (n + (q ++ B).length) = p ++ A ++ q ++ B := by
    rw [← List.rotate_rotate, hPi, show q ++ B ++ p ++ A = (q ++ B) ++ (p ++ A) by
      simp only [List.append_assoc], List.rotate_append_length_eq]
    simp only [List.append_assoc]
  exact CyclicArc.exists_darts_eq_of_rotate_eq h

/-- **Two arcs read backwards along one face walk share no dart.**  A face walk has no repeated
dart, and a common dart `d` of `p` and `q` puts `α d` in both reversed arcs. -/
theorem arcs_disjoint_of_face_walk {G : Type u} [Group G] {Lambda : Type w}
    {W : Set (List (RelLetter G Lambda))} {Delta : DiscDiagram.{u, w, v} W}
    {f : Delta.toCombMap.Face} {cycle : List Delta.toCombMap.Dart} (p q : CyclicArc cycle)
    {X Y : List Delta.toCombMap.Dart} {r : ℕ}
    (htrav : (Delta.faceBoundary f).darts.rotate r = X ++ q.reverseDarts ++ Y ++ p.reverseDarts) :
    ∀ d ∈ p.darts, d ∉ q.darts := by
  intro d hdp hdq
  have hnodup : (X ++ q.reverseDarts ++ Y ++ p.reverseDarts).Nodup := by
    rw [← htrav]
    exact List.nodup_rotate.mpr (Delta.faceBoundary f).nodup
  have hp : Delta.toCombMap.alpha d ∈ p.reverseDarts :=
    List.mem_map.mpr ⟨d, List.mem_reverse.mpr hdp, rfl⟩
  have hq : Delta.toCombMap.alpha d ∈ X ++ q.reverseDarts ++ Y :=
    List.mem_append_left _ (List.mem_append_right _
      (List.mem_map.mpr ⟨d, List.mem_reverse.mpr hdq, rfl⟩))
  exact List.disjoint_of_nodup_append hnodup hq hp

/-- **The decomposition of `∂Π`.**  If a face walk reads `X q⁻¹ Y p⁻¹` with `p` and `q` nonempty
arcs of cell `j`, some rotation of the carrier of `j` reads `q B p A`. -/
theorem exists_cellDarts_rotate_eq {G : Type u} [Group G] {Lambda : Type w}
    {W : Set (List (RelLetter G Lambda))} {Delta : DiscDiagram.{u, w, v} W}
    {f : Delta.toCombMap.Face} {j : Fin Delta.rCellCount}
    (sourceArc targetArc : CyclicArc (cellDarts Delta j)) {X Y : List Delta.toCombMap.Dart}
    {r : ℕ} (htrav : (Delta.faceBoundary f).darts.rotate r =
      X ++ targetArc.reverseDarts ++ Y ++ sourceArc.reverseDarts)
    (hs : 0 < sourceArc.length) (ht : 0 < targetArc.length) :
    ∃ (n : ℕ) (B A : List Delta.toCombMap.Dart),
      (cellDarts Delta j).rotate n = targetArc.darts ++ B ++ sourceArc.darts ++ A :=
  exists_rotate_eq_append_four targetArc sourceArc ht hs
    (arcs_disjoint_of_face_walk sourceArc targetArc htrav)

/-- **The value step when `X B` reads `1`.**  The face gives `Y = q X⁻¹ p` in `G`, and `B` reads
`X⁻¹`, so `q B p` reads `Y`. -/
theorem listVal_arc_eq_of_value_one_X {G : Type u} [Group G] {Lambda : Type w}
    {W : Set (List (RelLetter G Lambda))} {Delta : DiscDiagram.{u, w, v} W}
    {l X Y B p q : List Delta.toCombMap.Dart} (hl : RelLetter.listVal (dartWord Delta l) = 1)
    (hrot : l ~r X ++ invDarts Delta q ++ Y ++ invDarts Delta p)
    (hXB : RelLetter.listVal (dartWord Delta (X ++ B)) = 1) :
    RelLetter.listVal (dartWord Delta (q ++ B ++ p)) =
      RelLetter.listVal (dartWord Delta Y) := by
  have hface := Embedded.listVal_dartWord_eq_of_isRotated_invDarts Delta hl hrot
  rw [Embedded.dartWord_append, HullSC.RelWord.listVal_append] at hXB
  have hB := eq_inv_of_mul_eq_one_right hXB
  rw [Embedded.dartWord_append, HullSC.RelWord.listVal_append, Embedded.dartWord_append,
    HullSC.RelWord.listVal_append, hB, hface]

/-- **The value step when `Y A` reads `1`.**  The arc `p A q` reads `X`. -/
theorem listVal_arc_eq_of_value_one_Y {G : Type u} [Group G] {Lambda : Type w}
    {W : Set (List (RelLetter G Lambda))} {Delta : DiscDiagram.{u, w, v} W}
    {l X Y A p q : List Delta.toCombMap.Dart} (hl : RelLetter.listVal (dartWord Delta l) = 1)
    (hrot : l ~r X ++ invDarts Delta q ++ Y ++ invDarts Delta p)
    (hYA : RelLetter.listVal (dartWord Delta (Y ++ A)) = 1) :
    RelLetter.listVal (dartWord Delta (p ++ A ++ q)) =
      RelLetter.listVal (dartWord Delta X) := by
  have hrot' : l ~r Y ++ invDarts Delta p ++ X ++ invDarts Delta q := by
    refine hrot.trans ?_
    simpa only [List.append_assoc] using
      (List.isRotated_append (l := X ++ invDarts Delta q) (l' := Y ++ invDarts Delta p))
  exact listVal_arc_eq_of_value_one_X hl hrot' hYA

end CaseOneSameCell

open CaseOneWalk

/-- **The value-one kill across `X`.**  `htrav`, `hsource`, `htarget` and `hY` are as in
`osinLemma94CaseOneWalk_sameCell`.  If `T = q B p` is an arc of the cell and `X B` reads `1`, then
`T` reads `Y`, of word norm less than `ε`, while `q` and `p` read elements of word norm more than
`ε`.  So `T` is a hairpin and `λ ε - c < 2κ`. -/
theorem false_of_sameCell_value_one_X {G : Type u} [Group G] {Lambda : Type w}
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
    {X Y B : List S.diagram.toCombMap.Dart} {r : ℕ}
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
    (T : CyclicArc (cellDarts S.diagram j))
    (hT : T.darts = targetArc.darts ++ B ++ sourceArc.darts)
    (hXB : RelLetter.listVal (dartWord S.diagram (X ++ B)) = 1) : False := by
  have hp := lt_wordNorm_of_source_segment C hsource
  have hq := lt_wordNorm_of_target_segment C htarget
  rw [listVal_dartWord_reverseDarts_inv] at hp hq
  have hword := Embedded.CyclicArc.isLambdaCQuasiGeodesicWord_darts_cellDarts hW T
  rw [hT, Embedded.dartWord_append, Embedded.dartWord_append] at hword
  have hvalue := CaseOneSameCell.listVal_arc_eq_of_value_one_X (polygon_face_value P k)
    (polygon_face_isRotated P k htrav) hXB
  rw [Embedded.dartWord_append, Embedded.dartWord_append] at hvalue
  have hbound := hword.lambda_eps_lt_of_hairpin hmorse hlambda
    (by rw [hvalue]; exact wordNorm_lt_of_start_connector C hY) hq hp
  linarith

/-- **The value-one kill across `Y`.**  As `false_of_sameCell_value_one_X`, with `T = p A q`
reading `X` when `Y A` reads `1`. -/
theorem false_of_sameCell_value_one_Y {G : Type u} [Group G] {Lambda : Type w}
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
    {X Y A : List S.diagram.toCombMap.Dart} {r : ℕ}
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
    (T : CyclicArc (cellDarts S.diagram j))
    (hT : T.darts = sourceArc.darts ++ A ++ targetArc.darts)
    (hYA : RelLetter.listVal (dartWord S.diagram (Y ++ A)) = 1) : False := by
  have hp := lt_wordNorm_of_source_segment C hsource
  have hq := lt_wordNorm_of_target_segment C htarget
  rw [listVal_dartWord_reverseDarts_inv] at hp hq
  have hword := Embedded.CyclicArc.isLambdaCQuasiGeodesicWord_darts_cellDarts hW T
  rw [hT, Embedded.dartWord_append, Embedded.dartWord_append] at hword
  have hvalue := CaseOneSameCell.listVal_arc_eq_of_value_one_Y (polygon_face_value P k)
    (polygon_face_isRotated P k htrav) hYA
  rw [Embedded.dartWord_append, Embedded.dartWord_append] at hvalue
  have hbound := hword.lambda_eps_lt_of_hairpin hmorse hlambda
    (by rw [hvalue]; exact wordNorm_lt_of_end_connector C hX) hp hq
  linarith

/-- **Case 1 of Lemma 9.4 across one relator cell: the relator-cell branch.**
`OsinLemma94CaseOneSameCellStatement`, with the face walk data of
`osinLemma94CaseOneWalk_sameCell` and a rotation `q B p A` of the carrier of the cell as further
inputs, and with neither `X B` nor `Y A` reading `1`.  When one of them reads `1` the pair is
refuted by `false_of_sameCell_value_one_X` or `_Y`, so this statement gives
`OsinLemma94CaseOneSameCellStatement` (`osinLemma94CaseOneSameCell_of_rCell`); conversely that
statement gives this one.  In this branch the closed walks `X B` and `Y A` both read elements
other than `1`, so any pocket bounded by one of them holds a relator cell, and
`false_of_pocketRegion_of_below` refutes such a pocket once its cycles follow the boundary. -/
def OsinLemma94CaseOneRCellStatement : Prop :=
  ∀ {G : Type u} [Group G] {Lambda : Type w} (D : RelGenSet G Lambda),
    (∃ delta : ℕ, Hyperbolic.IsFourPointHyperbolic D.alphabet.carrier delta) →
    ∀ lambda c mu : ℝ, 0 < lambda → lambda ≤ 1 → 0 ≤ c → 0 < mu → mu ≤ 1 / 16 →
      ∃ eps0 : ℕ, ∀ eps : ℕ, eps0 ≤ eps →
        ∃ rho0 : ℕ, 0 < rho0 ∧ ∀ rho : ℕ, rho0 ≤ rho →
          ∀ (W : Set (List (RelLetter G Lambda))),
            OsinCCondition D W eps mu lambda c rho →
            ∀ (Delta : DiscDiagram.{u, w, v} W)
              (cuts : SectionCuts D lambda c Delta.boundaryWord),
              Delta.LeastArea → 0 < Delta.rCellCount →
              (∀ (Xi : DiscDiagram.{u, w, v} W)
                  (cutsXi : SectionCuts D lambda c Xi.boundaryWord),
                Xi.LeastArea → 0 < Xi.rCellCount → Xi.rCellCount < Delta.rCellCount →
                  ∃ T : RealizedSectionFamily D lambda c eps Xi cutsXi,
                    OsinLemma97bConclusion mu T) →
              ∀ S : GloballyDistinguishedSectionFamily D lambda c eps Delta cuts,
                S.family.card ≤ 3 * (Delta.rCellCount + cuts.count - 1) → S.DartMinimal →
                  ∀ P : OsinLemma94RealizedPolygons S, P.Maximal →
                    ∀ (k : Fin P.count) (C : WordConnectorPair (symmetricLabelAlphabet D)
                      (P.corner k) (P.word k) (P.sideCount k) (P.relatorSides k)
                      (P.longSides k) eps),
                      C.b' < C.b → P.kind k C.target ≠ .cutting →
                        P.kind k C.source = P.kind k C.target →
                        ∀ (j : Fin S.diagram.rCellCount)
                          (sourceArc targetArc : CyclicArc (cellDarts S.diagram j))
                          (X Y : List S.diagram.toCombMap.Dart) (r : ℕ),
                          P.kind k C.source = .cell j →
                          (S.diagram.faceBoundary (P.face k)).darts.rotate r =
                            X ++ targetArc.reverseDarts ++ Y ++ sourceArc.reverseDarts →
                          0 < sourceArc.length → 0 < targetArc.length →
                          vertex (P.corner k C.source) (P.word k C.source) C.a *
                              RelLetter.listVal (dartWord S.diagram sourceArc.reverseDarts) =
                            vertex (P.corner k C.source) (P.word k C.source) C.a' →
                          vertex (P.corner k C.target) (P.word k C.target) C.b' *
                              RelLetter.listVal (dartWord S.diagram targetArc.reverseDarts) =
                            vertex (P.corner k C.target) (P.word k C.target) C.b →
                          vertex (P.corner k C.source) (P.word k C.source) C.a' *
                              RelLetter.listVal (dartWord S.diagram X) =
                            vertex (P.corner k C.target) (P.word k C.target) C.b' →
                          vertex (P.corner k C.target) (P.word k C.target) C.b *
                              RelLetter.listVal (dartWord S.diagram Y) =
                            vertex (P.corner k C.source) (P.word k C.source) C.a →
                          ∀ (n : ℕ) (B A : List S.diagram.toCombMap.Dart),
                            (cellDarts S.diagram j).rotate n =
                              targetArc.darts ++ B ++ sourceArc.darts ++ A →
                            RelLetter.listVal (dartWord S.diagram (X ++ B)) ≠ 1 →
                            RelLetter.listVal (dartWord S.diagram (Y ++ A)) ≠ 1 → False

/-- **Case 1 of Lemma 9.4 across one relator cell, from the relator-cell branch.**  The face walk
reads `X q⁻¹ Y p⁻¹` and a rotation of the carrier of the cell reads `q B p A`.  If `X B` or `Y A`
reads `1`, the Morse threshold refutes the pair; otherwise the relator-cell branch does. -/
theorem osinLemma94CaseOneSameCell_of_rCell
    (hrcell : OsinLemma94CaseOneRCellStatement.{u, w, v}) :
    OsinLemma94CaseOneSameCellStatement.{u, w, v} := by
  intro G _ Lambda D hhyper lambda c mu hlambda hlambda1 hc hmu hmu1
  obtain ⟨kappa, hmorse, eps1, heps1⟩ :=
    exists_morse_threshold_of_fourPoint D hhyper lambda c hlambda
  obtain ⟨eps2, heps2⟩ := hrcell D hhyper lambda c mu hlambda hlambda1 hc hmu hmu1
  refine ⟨max eps1 eps2, fun eps heps => ?_⟩
  obtain ⟨rho0, hrho0, hrho⟩ := heps2 eps (le_of_max_le_right heps)
  refine ⟨rho0, hrho0, fun rho hrho' => ?_⟩
  intro W hW Delta cuts hleast hpos hbelow S hcard hmin P hmax k C hback hcut hsameKind
  obtain ⟨j, sourceArc, targetArc, X, Y, r, hj, htrav, hs, ht, hsource, htarget, hX, hY⟩ :=
    osinLemma94CaseOneWalk_sameCell P k C hback hsameKind
  obtain ⟨n, B, A, hPi⟩ :=
    CaseOneSameCell.exists_cellDarts_rotate_eq sourceArc targetArc htrav hs ht
  have hthreshold := heps1 eps (le_of_max_le_left heps)
  by_cases hXB : RelLetter.listVal (dartWord S.diagram (X ++ B)) = 1
  · obtain ⟨T, hT⟩ := CyclicArc.exists_darts_eq_of_rotate_eq hPi
    exact false_of_sameCell_value_one_X hW hlambda.le hmorse hthreshold P k C sourceArc
      targetArc htrav hsource htarget hY T hT hXB
  by_cases hYA : RelLetter.listVal (dartWord S.diagram (Y ++ A)) = 1
  · obtain ⟨T, hT⟩ := CaseOneSameCell.exists_arc_darts_eq_rotate_four hPi
    exact false_of_sameCell_value_one_Y hW hlambda.le hmorse hthreshold P k C sourceArc
      targetArc htrav hsource htarget hX T hT hYA
  exact hrho rho hrho' W hW Delta cuts hleast hpos hbelow S hcard hmin P hmax k C hback hcut
    hsameKind j sourceArc targetArc X Y r hj htrav hs ht hsource htarget hX hY n B A hPi hXB hYA

/-- **A pocket with a relator cell, refuted below `Δ`.**  Take an O-equivalent copy `X` of `Δ`
with letters as labels, and a pocket region of `X` whose cycles follow the boundary, with a
relator cell inside and a cell `i` outside, whose inverse complement cycle reads a side `s` of
word norm at most `ε` and an arc of `i` backwards.  The collar and the cell transport give a loop
cut of `Δ` (`nonempty_osinLoopCut_of_pocketRegion`).  If clause (b) of Lemma 9.7 holds below the
number of relator cells of `Δ` and `ρ` meets the width budget, `OsinLoopCut.false_of_below`
refutes the loop cut. -/
theorem false_of_pocketRegion_of_below (hcollar : GeodesicCollarStatement.{u, w, v})
    {G : Type u} [Group G] {Lambda : Type w} {W : Set (List (RelLetter G Lambda))}
    {D : RelGenSet G Lambda} {eps rho : ℕ} {mu lambda c : ℝ}
    (hW : OsinCCondition D W eps mu lambda c rho) (hlambda : 0 < lambda) (hlambda1 : lambda ≤ 1)
    (hc : 0 ≤ c) (hmu : 0 < mu) (hmu1 : mu ≤ 1 / 16) (hrho : 0 < rho)
    (hlarge : lambda⁻¹ * (3 * (eps : ℝ) + c) < mu / 2 * (rho : ℝ))
    {Delta X : DiscDiagram.{u, w, v} W} (hleast : Delta.LeastArea)
    (hbelow : ∀ (Xi : DiscDiagram.{u, w, v} W) (cutsXi : SectionCuts D lambda c Xi.boundaryWord),
      Xi.LeastArea → 0 < Xi.rCellCount → Xi.rCellCount < Delta.rCellCount →
        ∃ T : RealizedSectionFamily D lambda c eps Xi cutsXi, OsinLemma97bConclusion mu T)
    (equiv : OEquivalentDiscDiagram Delta X)
    (hlabel : ∀ d, (symmetricLabelAlphabet D).IsLetter (X.label d))
    (P : PocketRegion X) (hin : P.inner.FollowsBoundary) (hout : P.outer.FollowsBoundary)
    {C : RelatorCell X.toCombMap X.outerFace W} (hC : C ∈ X.relatorCells)
    (hCf : C.face ∈ P.faces) {i : Fin X.rCellCount} (hi : (cell X i).face ∉ P.faces)
    (A : CyclicArc (cellDarts X i)) (s : List X.toCombMap.Dart)
    (hdecomposition : invDarts X P.outer.cycle = s ++ invDarts X A.darts)
    (hnorm : WordMetric.wordNorm D.alphabet.carrier (RelLetter.listVal (dartWord X s)) ≤ eps) :
    False := by
  obtain ⟨cut⟩ := nonempty_osinLoopCut_of_pocketRegion hcollar pocketCellTransport hW hlambda1
    hc hleast equiv hlabel P hin hout hC hCf hi A s hdecomposition hnorm
  exact cut.false_of_below o52LeastArea hW hlambda hmu hmu1 hrho hlarge hleast
    (hbelow cut.enclosed cut.sections cut.leastArea cut.rCellCount_pos cut.rCellCount_lt)

end GroupApproximation.GGT.VanKampen

#audit_axioms GroupApproximation.GGT.VanKampen.CaseOneSameCell.exists_eq_append_four
#audit_axioms GroupApproximation.GGT.VanKampen.CaseOneSameCell.exists_rotate_eq_append_four
#audit_axioms GroupApproximation.GGT.VanKampen.CaseOneSameCell.exists_arc_darts_eq_rotate_four
#audit_axioms GroupApproximation.GGT.VanKampen.CaseOneSameCell.arcs_disjoint_of_face_walk
#audit_axioms GroupApproximation.GGT.VanKampen.CaseOneSameCell.exists_cellDarts_rotate_eq
#audit_axioms GroupApproximation.GGT.VanKampen.CaseOneSameCell.listVal_arc_eq_of_value_one_X
#audit_axioms GroupApproximation.GGT.VanKampen.CaseOneSameCell.listVal_arc_eq_of_value_one_Y
#audit_axioms GroupApproximation.GGT.VanKampen.false_of_sameCell_value_one_X
#audit_axioms GroupApproximation.GGT.VanKampen.false_of_sameCell_value_one_Y
#audit_axioms GroupApproximation.GGT.VanKampen.osinLemma94CaseOneSameCell_of_rCell
#audit_axioms GroupApproximation.GGT.VanKampen.false_of_pocketRegion_of_below
