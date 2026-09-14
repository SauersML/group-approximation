import GroupApproximation.GGT.VanKampen.Estimating.OsinUnboundCaseOneRun
import GroupApproximation.GGT.VanKampen.Estimating.OsinLemma94CaseOneWalkHolds
import GroupApproximation.Meta.AxiomGuard

/-!
# Case 1 of Osin's Lemma 9.4 for short connector pairs of different kinds

Osin (math/0411039v3, §9), proof of Lemma 9.4, Case 1.  A spanning class-word pair split at its gap
vertices gives pieces whose source and target lie inside single sides, with connectors of length at
most `ε`, but whose segments need not be longer than `ε`.  So a piece is no `WordConnectorPair`.  The
different-kind branch of Case 1 never reads the long clauses: the face walk (`osinLemma94CaseOneWalk`)
uses only the positions, and the region insertion (`RealizedSectionFamily.false_of_quadrilateral_face`)
uses only the connectors and nonempty arcs.

* `UnboundEstimate.ShortWordConnectorPair`: `WordConnectorPair` without `source_long` and
  `target_long`; `WordConnectorPair.toShort`.
* `UnboundEstimate.ShortWordConnectorPair.exists_nonempty_connectors`.
* `osinLemma94ShortCaseOneWalk`: the face walk `X ++ T ++ Y ++ P` for a short pair.
* `osinLemma94ShortCaseOne_false`: a backwards short pair whose target side is not a cutting path and
  whose two sides have different kinds gives a contradiction, once `ε ≥ 3`.

The same-cell branch (the Morse kills of `osinLemma94CaseOneSameCell_of_rCell` read long ends) and the
cutting targets (Case 2 counts darts against `target_long`) are not covered here.

## Manuscript status

Infrastructure for `thm:hull` (tex 1636, "Hull's small cancellation theorem", through Osin's
Lemma 9.4 inside the proof of Lemma 4.4); certifies no printed sentence on its own.
-/

namespace GroupApproximation.GGT.VanKampen.UnboundEstimate

open GroupApproximation.WordMetric GroupApproximation.HullSC OsinComponents

universe u w

variable {G : Type u} [Group G] {Lambda : Type w}

/-- **A short connector pair**: a `WordConnectorPair` without the two long clauses. -/
structure ShortWordConnectorPair (D : RelGenSet G Lambda) (v : ℕ → G)
    (word : ℕ → List (RelLetter G Lambda)) (n : ℕ) (A B : Set ℕ) (eps : ℕ) where
  source : ℕ
  target : ℕ
  source_lt : source < n
  target_lt : target < n
  source_mem : source ∈ A
  target_mem : target ∈ B
  distinct : source ≠ target
  source_admissible : RelWord.IsAdmissible D (word source)
  target_admissible : RelWord.IsAdmissible D (word target)
  a : ℕ
  a' : ℕ
  b : ℕ
  b' : ℕ
  a_le : a ≤ (word source).length
  a'_le : a' ≤ (word source).length
  b_le : b ≤ (word target).length
  b'_le : b' ≤ (word target).length
  source_forward : a < a'
  startConnector : List (RelLetter G Lambda)
  endConnector : List (RelLetter G Lambda)
  start_geodesic : IsGeodesicWord D
    (vertex (v target) (word target) b) (vertex (v source) (word source) a) startConnector
  end_geodesic : IsGeodesicWord D
    (vertex (v source) (word source) a') (vertex (v target) (word target) b') endConnector
  start_short : startConnector.length < eps
  end_short : endConnector.length < eps

variable {D : RelGenSet G Lambda} {v : ℕ → G}
  {word : ℕ → List (RelLetter G Lambda)} {n eps : ℕ} {A B : Set ℕ}

/-- Every connector pair is a short pair. -/
def WordConnectorPair.toShort (C : WordConnectorPair D v word n A B eps) :
    ShortWordConnectorPair D v word n A B eps where
  source := C.source
  target := C.target
  source_lt := C.source_lt
  target_lt := C.target_lt
  source_mem := C.source_mem
  target_mem := C.target_mem
  distinct := C.distinct
  source_admissible := C.source_admissible
  target_admissible := C.target_admissible
  a := C.a
  a' := C.a'
  b := C.b
  b' := C.b'
  a_le := C.a_le
  a'_le := C.a'_le
  b_le := C.b_le
  b'_le := C.b'_le
  source_forward := C.source_forward
  startConnector := C.startConnector
  endConnector := C.endConnector
  start_geodesic := C.start_geodesic
  end_geodesic := C.end_geodesic
  start_short := C.start_short
  end_short := C.end_short

/-- **Nonempty connectors for a short pair**, as `WordConnectorPair.exists_nonempty_connectors`. -/
theorem ShortWordConnectorPair.exists_nonempty_connectors
    (C : ShortWordConnectorPair D v word n A B eps)
    (hsymm : ∀ x ∈ D.base, x⁻¹ ∈ D.base) (heps : 2 < eps) :
    ∃ startWord endWord : List (RelLetter G Lambda),
      startWord ≠ [] ∧ endWord ≠ [] ∧ RelWord.IsAdmissible D startWord ∧
        RelWord.IsAdmissible D endWord ∧
        RelLetter.listVal startWord = RelLetter.listVal C.startConnector ∧
        RelLetter.listVal endWord = RelLetter.listVal C.endConnector ∧
        startWord.length < eps ∧ endWord.length < eps := by
  have hne : word C.source ≠ [] := by
    intro h
    have hle := C.a'_le
    have hlt := C.source_forward
    rw [h, List.length_nil] at hle
    omega
  obtain ⟨letter, hletter⟩ : ∃ letter : RelLetter G Lambda, D.IsLetter letter :=
    ⟨(word C.source).head hne, C.source_admissible _ (List.head_mem hne)⟩
  exact ⟨NonemptyConnectorWord.word letter C.startConnector,
    NonemptyConnectorWord.word letter C.endConnector,
    NonemptyConnectorWord.nonempty _ _, NonemptyConnectorWord.nonempty _ _,
    NonemptyConnectorWord.admissible D hsymm letter hletter _ C.start_geodesic.1,
    NonemptyConnectorWord.admissible D hsymm letter hletter _ C.end_geodesic.1,
    NonemptyConnectorWord.value _ _, NonemptyConnectorWord.value _ _,
    NonemptyConnectorWord.length_lt _ _ heps C.start_short,
    NonemptyConnectorWord.length_lt _ _ heps C.end_short⟩

end GroupApproximation.GGT.VanKampen.UnboundEstimate

namespace GroupApproximation.GGT.VanKampen

universe u w v

open GroupApproximation.GGT.VanKampen.Embedded
open GroupApproximation.GGT.VanKampen.UnboundEstimate
open GroupApproximation.GGT.OsinComponents
open CaseOneWalk

/-- **The Case 1 face walk for a short pair.**  As `osinLemma94CaseOneWalk`, which reads only the
positions of the pair. -/
theorem osinLemma94ShortCaseOneWalk {G : Type u} [Group G] {Lambda : Type w}
    {W : Set (List (RelLetter G Lambda))}
    {D E : RelGenSet G Lambda} {lambda c : ℝ} {eps : ℕ}
    {Delta : DiscDiagram.{u, w, v} W} {cuts : SectionCuts D lambda c Delta.boundaryWord}
    {S : GloballyDistinguishedSectionFamily D lambda c eps Delta cuts}
    (P : OsinLemma94RealizedPolygons S) (k : Fin P.count)
    (C : ShortWordConnectorPair E (P.corner k) (P.word k) (P.sideCount k) (P.relatorSides k)
      (P.longSides k) eps)
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

/-- **Case 1 for a short pair of different kinds.**  Once `ε ≥ 3`, a backwards short pair of polygon
`k` whose target side is not a cutting path, and whose two sides have different kinds, gives a
contradiction. -/
theorem osinLemma94ShortCaseOne_false {G : Type u} [Group G] {Lambda : Type w}
    {W : Set (List (RelLetter G Lambda))}
    {D : RelGenSet G Lambda} {lambda c : ℝ} {eps : ℕ} (heps : 3 ≤ eps)
    {Delta : DiscDiagram.{u, w, v} W} {cuts : SectionCuts D lambda c Delta.boundaryWord}
    {S : GloballyDistinguishedSectionFamily D lambda c eps Delta cuts}
    (P : OsinLemma94RealizedPolygons S) (k : Fin P.count)
    (C : ShortWordConnectorPair (symmetricLabelAlphabet D) (P.corner k) (P.word k)
      (P.sideCount k) (P.relatorSides k) (P.longSides k) eps)
    (hback : C.b' < C.b) (hcut : P.kind k C.target ≠ .cutting)
    (hkind : P.kind k C.source ≠ P.kind k C.target) : False := by
  obtain ⟨source, target, sourceArc, targetArc, X, Y, r, htrav, hsource, htarget, hks, hkt,
    hsection, hX, hY⟩ := osinLemma94ShortCaseOneWalk P k C hback hcut
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
    have h := le_of_lt C.end_short
    rw [hlen] at h
    exact h
  have hnorm2 : WordMetric.wordNorm D.alphabet.carrier (RelLetter.listVal startWord) ≤ eps := by
    obtain ⟨-, hmul, hlen⟩ := C.start_geodesic
    rw [hsval, eq_inv_mul_of_mul_eq hmul, ← symmetricLabelAlphabet.wordNorm_eq D]
    have h := le_of_lt C.start_short
    rw [hlen] at h
    exact h
  exact RealizedSectionFamily.false_of_quadrilateral_face S.toRealizedSectionFamily
    S.label_admissible S.weight_maximal (P.face k) (P.face_ne_outer k) hcells
    (P.face_unselected k) source target sourceArc targetArc X Y r htrav hsource htarget
    hsection hloop endWord startWord hene hsne headm
    (fun l hl => HullSC.isLetter_relWordInv _ hsymm (headm l hl))
    hsadm
    (fun l hl => HullSC.isLetter_relWordInv _ hsymm (hsadm l hl))
    hval1 hval2 (le_of_lt heshort) (le_of_lt hsshort) hnorm1 hnorm2

end GroupApproximation.GGT.VanKampen

#audit_axioms GroupApproximation.GGT.VanKampen.UnboundEstimate.ShortWordConnectorPair.exists_nonempty_connectors
#audit_axioms GroupApproximation.GGT.VanKampen.osinLemma94ShortCaseOneWalk
#audit_axioms GroupApproximation.GGT.VanKampen.osinLemma94ShortCaseOne_false
