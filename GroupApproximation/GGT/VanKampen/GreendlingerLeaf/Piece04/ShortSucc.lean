import GroupApproximation.GGT.VanKampen.Estimating.OsinLemma94ShortCaseOne
import GroupApproximation.Meta.AxiomGuard

/-!
# Greendlinger leaf, piece 04: short Case 1 with connectors of length at most `ε`

Osin, arXiv:math/0411039v3, §9, proof of Lemma 9.4, Case 1.  `osinLemma94ShortCaseOne_false` takes
a short pair with connectors shorter than `ε`, the parameter of the section family.  The region
insertion it ends with (`RealizedSectionFamily.false_of_quadrilateral_face`) only needs connector
words of length and norm at most `ε`.  So the same refutation holds for a short pair at parameter
`ε + 1`, whose connectors have length at most `ε`.

* `shortCaseOneWalk`: the face walk of `osinLemma94ShortCaseOneWalk`, with the connector parameter
  of the pair independent of that of the section family.  The walk reads only the positions of the
  pair, so the proof is the same.
* `false_of_shortPair_succ`: a backwards short pair at parameter `ε + 1` whose target side is not a
  cutting path and whose two sides have different kinds gives a contradiction, once `ε ≥ 3`.  The
  nonempty connector words have length `< ε + 1`, so `≤ ε`, and their norms are the connector
  lengths.

## Manuscript status

Infrastructure for `thm:hull` (Hull's small cancellation theorem, through Osin's Lemma 9.4);
certifies no printed sentence on its own.
-/

namespace GroupApproximation.GGT.VanKampen.GreendlingerLeaf.Piece04

universe u w v

open GroupApproximation.GGT.VanKampen.Embedded
open GroupApproximation.GGT.VanKampen.UnboundEstimate
open GroupApproximation.GGT.OsinComponents
open GroupApproximation.GGT.VanKampen.CaseOneWalk

/-- **The Case 1 face walk for a short pair, at any connector parameter.**  As
`osinLemma94ShortCaseOneWalk`, which reads only the positions of the pair. -/
theorem shortCaseOneWalk {G : Type u} [Group G] {Lambda : Type w}
    {W : Set (List (RelLetter G Lambda))}
    {D E : RelGenSet G Lambda} {lambda c : ℝ} {eps eps' : ℕ}
    {Delta : DiscDiagram.{u, w, v} W} {cuts : SectionCuts D lambda c Delta.boundaryWord}
    {S : GloballyDistinguishedSectionFamily D lambda c eps Delta cuts}
    (P : OsinLemma94RealizedPolygons S) (k : Fin P.count)
    (C : ShortWordConnectorPair E (P.corner k) (P.word k) (P.sideCount k) (P.relatorSides k)
      (P.longSides k) eps')
    (hbb : C.b' < C.b) (hcut : P.kind k C.target ≠ .cutting) :
    ∃ (source : Fin S.diagram.rCellCount) (target : Option (Fin S.diagram.rCellCount))
      (sourceArc : CyclicArc (cellDarts S.diagram source))
      (targetArc : CyclicArc (targetDarts S.diagram target))
      (X Y : List S.diagram.toCombMap.Dart) (r : ℕ),
      (S.diagram.faceBoundary (P.face k)).darts.rotate r =
          X ++ targetBoundaryDarts S.diagram target targetArc ++ Y ++
            sourceArc.reverseDarts ∧
        0 < sourceArc.length ∧ 0 < targetArc.length ∧
        P.kind k C.source = .cell source ∧
        (∀ j, target = some j → P.kind k C.target = .cell j) ∧
        (target = none → ∃ j : Fin cuts.count,
          cuts.cut j.castSucc ≤ targetArc.start.val ∧
            targetArc.start.val + targetArc.length ≤ cuts.cut j.succ) ∧
        vertex (P.corner k C.source) (P.word k C.source) C.a' *
            RelLetter.listVal (dartWord S.diagram X) =
          vertex (P.corner k C.target) (P.word k C.target) C.b' ∧
        vertex (P.corner k C.target) (P.word k C.target) C.b *
            RelLetter.listVal (dartWord S.diagram Y) =
          vertex (P.corner k C.source) (P.word k C.source) C.a := by
  obtain ⟨j, hj⟩ : ∃ j, P.kind k C.source = .cell j := C.source_mem
  have htgt : P.kind k C.target ≠ .short := C.target_mem
  have hs := C.source_lt
  have ht := C.target_lt
  have hfwd := C.source_forward
  have ha' : C.a' ≤ (P.sideDarts k C.source).length :=
    C.a'_le.trans_eq (polygon_length_word P k _)
  have hb : C.b ≤ (P.sideDarts k C.target).length :=
    C.b_le.trans_eq (polygon_length_word P k _)
  obtain ⟨X, Y, r, hrot, hX, hY⟩ :=
    polygon_four_windows P k hs ht C.distinct (le_of_lt hfwd) ha' (le_of_lt hbb) hb
  obtain ⟨sarc, hsarc⟩ := P.cell_arc k C.source j hs hj
  have hsl : (P.sideDarts k C.source).length = sarc.length := by
    rw [hsarc, cyclicArc_length_reverseDarts]
  obtain ⟨sarc', hslen, hsdarts⟩ :=
    cyclicArc_exists_sub_reverse sarc C.a (C.a' - C.a) (by omega)
  rw [hsarc, ← hsdarts] at hrot
  have hs0 : 0 < sarc'.length := by
    rw [hslen]
    omega
  cases hkt : P.kind k C.target with
  | cutting => exact absurd hkt hcut
  | short => exact absurd hkt htgt
  | cell j' =>
    obtain ⟨tarc, htarc⟩ := P.cell_arc k C.target j' ht hkt
    have htl : (P.sideDarts k C.target).length = tarc.length := by
      rw [htarc, cyclicArc_length_reverseDarts]
    obtain ⟨tarc', htlen, htdarts⟩ :=
      cyclicArc_exists_sub_reverse tarc C.b' (C.b - C.b') (by omega)
    rw [htarc, ← htdarts] at hrot
    have h0 : 0 < tarc'.length := by
      rw [htlen]
      omega
    refine ⟨j, some j', sarc', tarc', X, Y, r, hrot, hs0, h0, hj, ?_, ?_, hX, hY⟩
    · intro j0 h
      cases h
      rfl
    · intro h
      cases h
  | boundary j' =>
    obtain ⟨hj', barc, hbsd, hlo, hhi⟩ := P.boundary_arc k C.target j' ht hkt
    have hbl : (P.sideDarts k C.target).length = barc.length := by
      rw [hbsd, CyclicArc.darts_length]
    obtain ⟨tarc', htlen, htdarts, htstart⟩ :=
      cyclicArc_exists_sub barc C.b' (C.b - C.b') (by omega)
    rw [hbsd, ← htdarts] at hrot
    have hcyc : (targetDarts S.diagram none).length = Delta.boundaryWord.length := by
      have e := congrArg List.length (dartWord_outerDarts S.diagram)
      rw [S.equiv.boundaryWord_eq, dartWord, List.length_map] at e
      exact e
    have hlo' : cuts.cut (Fin.castSucc ⟨j', hj'⟩) ≤ barc.start.1 := hlo
    have hhi' : barc.start.1 + barc.length ≤ cuts.cut (Fin.succ ⟨j', hj'⟩) := hhi
    have hlast := cuts.cut_mono (Fin.le_last (Fin.succ (⟨j', hj'⟩ : Fin cuts.count)))
    rw [cuts.cut_last] at hlast
    have hst' := htstart (by omega)
    have h0 : 0 < tarc'.length := by
      rw [htlen]
      omega
    refine ⟨j, none, sarc', tarc', X, Y, r, hrot, hs0, h0, hj, ?_, ?_, hX, hY⟩
    · intro j0 h
      cases h
    · intro _
      refine ⟨⟨j', hj'⟩, ?_, ?_⟩
      · rw [hst']
        omega
      · rw [hst', htlen]
        omega

/-- **Case 1 for a short pair of different kinds, with connectors of length at most `ε`.**  Once
`ε ≥ 3`, a backwards short pair at parameter `ε + 1` of polygon `k`, whose target side is not a
cutting path and whose two sides have different kinds, gives a contradiction. -/
theorem false_of_shortPair_succ {G : Type u} [Group G] {Lambda : Type w}
    {W : Set (List (RelLetter G Lambda))}
    {D : RelGenSet G Lambda} {lambda c : ℝ} {eps : ℕ} (heps : 3 ≤ eps)
    {Delta : DiscDiagram.{u, w, v} W} {cuts : SectionCuts D lambda c Delta.boundaryWord}
    {S : GloballyDistinguishedSectionFamily D lambda c eps Delta cuts}
    (P : OsinLemma94RealizedPolygons S) (k : Fin P.count)
    (C : ShortWordConnectorPair (symmetricLabelAlphabet D) (P.corner k) (P.word k)
      (P.sideCount k) (P.relatorSides k) (P.longSides k) (eps + 1))
    (hback : C.b' < C.b) (hcut : P.kind k C.target ≠ .cutting)
    (hkind : P.kind k C.source ≠ P.kind k C.target) : False := by
  obtain ⟨source, target, sourceArc, targetArc, X, Y, r, htrav, hsource, htarget, hks, hkt,
    hsection, hX, hY⟩ := shortCaseOneWalk P k C hback hcut
  have hloop : target ≠ some source := fun h => hkind (hks.trans (hkt source h).symm)
  have hsymm := symmetricLabelAlphabet.symmetric D
  obtain ⟨startWord, endWord, hsne, hene, hsadm, headm, hsval, heval, hsshort, heshort⟩ :=
    C.exists_nonempty_connectors hsymm (by omega)
  have hcells : ∀ cell ∈ S.diagram.relatorCells, cell.face ≠ P.face k := by
    intro cell hcell
    obtain ⟨j, rfl⟩ := List.mem_iff_get.mp hcell
    exact P.face_not_cell k j
  have hval1 : RelLetter.listVal endWord = RelLetter.listVal (dartWord S.diagram X) :=
    heval.trans (mul_left_cancel (C.end_geodesic.2.1.trans hX.symm))
  have hval2 : RelLetter.listVal startWord = RelLetter.listVal (dartWord S.diagram Y) :=
    hsval.trans (mul_left_cancel (C.start_geodesic.2.1.trans hY.symm))
  have hnorm1 : WordMetric.wordNorm D.alphabet.carrier (RelLetter.listVal endWord) ≤ eps := by
    obtain ⟨-, hmul, hlen⟩ := C.end_geodesic
    rw [heval, eq_inv_mul_of_mul_eq hmul, ← symmetricLabelAlphabet.wordNorm_eq D]
    have h : C.endConnector.length ≤ eps := by
      have := C.end_short
      omega
    rw [hlen] at h
    exact h
  have hnorm2 : WordMetric.wordNorm D.alphabet.carrier (RelLetter.listVal startWord) ≤ eps := by
    obtain ⟨-, hmul, hlen⟩ := C.start_geodesic
    rw [hsval, eq_inv_mul_of_mul_eq hmul, ← symmetricLabelAlphabet.wordNorm_eq D]
    have h : C.startConnector.length ≤ eps := by
      have := C.start_short
      omega
    rw [hlen] at h
    exact h
  exact RealizedSectionFamily.false_of_quadrilateral_face S.toRealizedSectionFamily
    S.label_admissible S.weight_maximal (P.face k) (P.face_ne_outer k) hcells
    (P.face_unselected k) source target sourceArc targetArc X Y r htrav hsource htarget
    hsection hloop endWord startWord hene hsne headm
    (fun l hl => HullSC.isLetter_relWordInv _ hsymm (headm l hl))
    hsadm
    (fun l hl => HullSC.isLetter_relWordInv _ hsymm (hsadm l hl))
    hval1 hval2 (by omega) (by omega) hnorm1 hnorm2

end GroupApproximation.GGT.VanKampen.GreendlingerLeaf.Piece04

#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.Piece04.shortCaseOneWalk
#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.Piece04.false_of_shortPair_succ
