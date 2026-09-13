import GroupApproximation.GGT.VanKampen.Estimating.OsinUnboundCaseOneFace
import GroupApproximation.GGT.VanKampen.Estimating.OsinLemma94PolygonClasses
import GroupApproximation.Meta.AxiomGuard

/-!
# Case 1 of Osin's Lemma 9.4 through a pinched window

In Case 1 of the proof of Osin's Appendix Lemma 9.4 (arXiv:math/0411039v3), the connectors of a
backwards pair cut a quadrilateral out of a component polygon, and "This contradicts the
maximality of `M`."  On a pinched relator cell, a class of the polygon is one arc of the cell only
together with the gaps between its sides (`OsinLemma94ClassPolygons.cell_arc`).  A gap is a closed
path of value one along the cell, off the face walk.  A window of a class through a junction
reads only the sides on the face walk, while the arc of the cell also reads the gap.  So the walk
of the face does not read the arc from across, and
`RealizedSectionFamily.false_of_quadrilateral_face` does not apply.

`OsinLemma94PinchedQuadrilateralStatement` is the quadrilateral member that accepts such windows.
Each arc is a list of pieces `(side, gap)`: every side is nonempty, every gap reads the identity,
and the last piece has no gap.  The face walk reads `X`, the sides of the target arc, `Y` and the
sides of the source arc.

* `OsinLemma94PinchedQuadrilateralStatement.false_of_quadrilateral`: with one piece per arc,
  the statement gives the contradiction of `false_of_quadrilateral_face` on a least-area diagram.
* `OsinLemma94ClassPolygons.pinchedPieces`: the pieces of a class.  A class of kind `cell j` or
  `boundary j` meets the piece hypotheses (`exists_cellArc_pinchedPieces`,
  `exists_boundaryArc_pinchedPieces`, `pinchedPieces_spec`, `pinchedPieces_getLast?`).

## Model test

audit-intro's pinched cell: `n = 1`, `λ = 1/8`, `c = 3`, and one relator cell `Π` reading
`g_1 abc g_2 abc ⋯ g_{t+1}` with `abc = 1`, pinched at every `abc`.  The loop `abc` closes at a
vertex `v` and bounds a `G`-face `B`.
* Not vacuous.  Take the polygon face `f` across an (A1) class of `Π` through a pinch, and a
  family without maximal weight.  A window through the pinch is `[(side, abc), (side, [])]`, and
  every hypothesis but maximality holds.  `false_of_quadrilateral_face` does not apply there: at
  the junction `P.Maximal` gives `facePerm (alpha e') ≠ alpha e`, so the walk of `f` never reads a
  `CyclicArc.reverseDarts` through the pinch.
* True on the model.  Split `v` at a corner of `B` and the corner of `f` (`PinchSplit.Input`).
  The cell is no longer pinched, `f` and `B` merge into one face whose walk reads the gap, and the
  family moves with its weight and card (`PinchSplit.transportDistinguished`).  Then
  `false_of_quadrilateral_face` on the merged face contradicts maximality.
* The same route in general.  A gap that bounds several faces is first collapsed to one face, a
  spur along a cell is first opened (`SurgeryFaceEdgeDoubling`), and a spur of `∂Δ` is first
  thickened (`SurgeryOuterSpurThickening`).
* Least area is used.  The diagram of `S` has least area too, since `S.equiv` keeps the boundary
  word and the number of relator cells.  The disc bounded by a gap lies on the side of the loop
  away from the cell and reads the identity, so it holds no relator cell, and no selected region,
  whose two ends would both lie on the gap.

## Manuscript status

Infrastructure for `thm:hull` (Hull's small cancellation theorem, through Osin's Lemma 4.4);
certifies no printed sentence on its own.
-/

namespace GroupApproximation.GGT.VanKampen

universe u w v

open GroupApproximation.GGT.VanKampen.Embedded

/-- **Case 1 of Lemma 9.4 through pinched windows.**  "Case 1 … This contradicts the maximality of
`M`."  Let `S` be the optimal section family of a least-area diagram, and `f` an inner face of its
diagram that is no relator cell and lies in no selected region.  Let `p` be a nonempty arc of a
relator cell and `q` a nonempty arc of a different relator cell or of `∂Δ` inside one section,
both read as a region boundary reads them.  Suppose that each splits into pieces `(side, gap)`,
where every side is nonempty, every gap reads the identity and the last piece has no gap, and that
some rotation of the walk of `f` reads `X`, the sides of `q`, `Y` and the sides of `p`.  If `s_1`,
`s_2` are legal words of length and norm at most `ε` with the values of `X` and `Y`, there is a
contradiction. -/
def OsinLemma94PinchedQuadrilateralStatement : Prop :=
  ∀ {G : Type u} [Group G] {Lambda : Type w} {W : Set (List (RelLetter G Lambda))}
    {D : RelGenSet G Lambda} {lambda c : ℝ} {eps : ℕ}
    {Delta : DiscDiagram.{u, w, v} W} {cuts : SectionCuts D lambda c Delta.boundaryWord}
    (S : GloballyDistinguishedSectionFamily D lambda c eps Delta cuts),
    Delta.LeastArea →
    ∀ f : S.diagram.toCombMap.Face, f ≠ S.diagram.outerFace →
      (∀ C ∈ S.diagram.relatorCells, C.face ≠ f) → (∀ a ∈ S.family, f ∉ a.1) →
    ∀ (source : Fin S.diagram.rCellCount) (target : Option (Fin S.diagram.rCellCount))
      (sourceArc : CyclicArc (cellDarts S.diagram source))
      (targetArc : CyclicArc (targetDarts S.diagram target))
      (sourcePieces targetPieces :
        List (List S.diagram.toCombMap.Dart × List S.diagram.toCombMap.Dart))
      (X Y : List S.diagram.toCombMap.Dart) (r : ℕ),
      sourceArc.reverseDarts = sourcePieces.flatMap (fun p => p.1 ++ p.2) →
      targetBoundaryDarts S.diagram target targetArc =
        targetPieces.flatMap (fun p => p.1 ++ p.2) →
      (∀ p ∈ sourcePieces ++ targetPieces,
        p.1 ≠ [] ∧ RelLetter.listVal (dartWord S.diagram p.2) = 1) →
      (∀ p ∈ sourcePieces.getLast?, p.2 = []) → (∀ p ∈ targetPieces.getLast?, p.2 = []) →
      (S.diagram.faceBoundary f).darts.rotate r =
        X ++ targetPieces.flatMap Prod.fst ++ Y ++ sourcePieces.flatMap Prod.fst →
      0 < sourceArc.length → 0 < targetArc.length →
      (target = none → ∃ j : Fin cuts.count,
        cuts.cut j.castSucc ≤ targetArc.start.val ∧
          targetArc.start.val + targetArc.length ≤ cuts.cut j.succ) →
      target ≠ some source →
      ∀ s1 s2 : List (RelLetter G Lambda), s1 ≠ [] → s2 ≠ [] →
        HullSC.RelWord.IsAdmissible (symmetricLabelAlphabet D) s1 →
        (∀ l ∈ s1, (symmetricLabelAlphabet D).IsLetter (HullSC.RelWord.inv l)) →
        HullSC.RelWord.IsAdmissible (symmetricLabelAlphabet D) s2 →
        (∀ l ∈ s2, (symmetricLabelAlphabet D).IsLetter (HullSC.RelWord.inv l)) →
        RelLetter.listVal s1 = RelLetter.listVal (dartWord S.diagram X) →
        RelLetter.listVal s2 = RelLetter.listVal (dartWord S.diagram Y) →
        s1.length ≤ eps → s2.length ≤ eps →
        WordMetric.wordNorm D.alphabet.carrier (RelLetter.listVal s1) ≤ eps →
        WordMetric.wordNorm D.alphabet.carrier (RelLetter.listVal s2) ≤ eps → False

namespace Embedded

/-- A reversed arc of positive length is nonempty. -/
theorem reverseDarts_ne_nil_of_length_pos {M : CombMap.{v}} {cycle : List M.Dart}
    (arc : CyclicArc cycle) (h : 0 < arc.length) : arc.reverseDarts ≠ [] := by
  apply List.ne_nil_of_length_pos
  simp only [CyclicArc.reverseDarts, List.length_map, List.length_reverse,
    CyclicArc.darts_length]
  exact h

/-- A target arc of positive length reads a nonempty boundary. -/
theorem targetBoundaryDarts_ne_nil_of_length_pos {G : Type u} [Group G] {Lambda : Type w}
    {W : Set (List (RelLetter G Lambda))} {Delta : DiscDiagram.{u, w, v} W}
    {target : Option (Fin Delta.rCellCount)} (arc : CyclicArc (targetDarts Delta target))
    (h : 0 < arc.length) : targetBoundaryDarts Delta target arc ≠ [] := by
  apply List.ne_nil_of_length_pos
  cases target with
  | none =>
    simp only [targetBoundaryDarts, CyclicArc.darts_length]
    exact h
  | some _ =>
    simp only [targetBoundaryDarts, CyclicArc.reverseDarts, List.length_map,
      List.length_reverse, CyclicArc.darts_length]
    exact h

end Embedded

namespace OsinLemma94PinchedQuadrilateralStatement

/-- **One piece per arc.**  With no gap, the statement gives the contradiction of
`RealizedSectionFamily.false_of_quadrilateral_face` for the optimal section family of a
least-area diagram. -/
theorem false_of_quadrilateral (h : OsinLemma94PinchedQuadrilateralStatement.{u, w, v})
    {G : Type u} [Group G] {Lambda : Type w} {W : Set (List (RelLetter G Lambda))}
    {D : RelGenSet G Lambda} {lambda c : ℝ} {eps : ℕ}
    {Delta : DiscDiagram.{u, w, v} W} {cuts : SectionCuts D lambda c Delta.boundaryWord}
    (S : GloballyDistinguishedSectionFamily D lambda c eps Delta cuts) (hleast : Delta.LeastArea)
    (f : S.diagram.toCombMap.Face) (hf : f ≠ S.diagram.outerFace)
    (hcells : ∀ C ∈ S.diagram.relatorCells, C.face ≠ f) (havoid : ∀ a ∈ S.family, f ∉ a.1)
    (source : Fin S.diagram.rCellCount) (target : Option (Fin S.diagram.rCellCount))
    (sourceArc : CyclicArc (cellDarts S.diagram source))
    (targetArc : CyclicArc (targetDarts S.diagram target))
    (X Y : List S.diagram.toCombMap.Dart) (r : ℕ)
    (htrav : (S.diagram.faceBoundary f).darts.rotate r =
      X ++ targetBoundaryDarts S.diagram target targetArc ++ Y ++ sourceArc.reverseDarts)
    (hsource : 0 < sourceArc.length) (htarget : 0 < targetArc.length)
    (hsection : target = none → ∃ j : Fin cuts.count,
      cuts.cut j.castSucc ≤ targetArc.start.val ∧
        targetArc.start.val + targetArc.length ≤ cuts.cut j.succ)
    (hloop : target ≠ some source)
    (s1 s2 : List (RelLetter G Lambda)) (hne1 : s1 ≠ []) (hne2 : s2 ≠ [])
    (hadm1 : HullSC.RelWord.IsAdmissible (symmetricLabelAlphabet D) s1)
    (hinv1 : ∀ l ∈ s1, (symmetricLabelAlphabet D).IsLetter (HullSC.RelWord.inv l))
    (hadm2 : HullSC.RelWord.IsAdmissible (symmetricLabelAlphabet D) s2)
    (hinv2 : ∀ l ∈ s2, (symmetricLabelAlphabet D).IsLetter (HullSC.RelWord.inv l))
    (hval1 : RelLetter.listVal s1 = RelLetter.listVal (dartWord S.diagram X))
    (hval2 : RelLetter.listVal s2 = RelLetter.listVal (dartWord S.diagram Y))
    (hlen1 : s1.length ≤ eps) (hlen2 : s2.length ≤ eps)
    (hnorm1 : WordMetric.wordNorm D.alphabet.carrier (RelLetter.listVal s1) ≤ eps)
    (hnorm2 : WordMetric.wordNorm D.alphabet.carrier (RelLetter.listVal s2) ≤ eps) :
    False := by
  have hsne := reverseDarts_ne_nil_of_length_pos sourceArc hsource
  have htne := targetBoundaryDarts_ne_nil_of_length_pos targetArc htarget
  refine h S hleast f hf hcells havoid source target sourceArc targetArc
    [(sourceArc.reverseDarts, [])] [(targetBoundaryDarts S.diagram target targetArc, [])] X Y r
    ?_ ?_ ?_ ?_ ?_ ?_ hsource htarget hsection hloop s1 s2 hne1 hne2 hadm1 hinv1 hadm2 hinv2
    hval1 hval2 hlen1 hlen2 hnorm1 hnorm2
  · simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil]
  · simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil]
  · intro p hp
    rcases List.mem_append.mp hp with hp | hp
    · rw [List.mem_singleton] at hp
      subst hp
      exact ⟨hsne, rfl⟩
    · rw [List.mem_singleton] at hp
      subst hp
      exact ⟨htne, rfl⟩
  · intro p hp
    rw [List.getLast?_singleton, Option.mem_def, Option.some.injEq] at hp
    subst hp
    rfl
  · intro p hp
    rw [List.getLast?_singleton, Option.mem_def, Option.some.injEq] at hp
    subst hp
    rfl
  · simpa only [List.flatMap_cons, List.flatMap_nil, List.append_nil] using htrav

end OsinLemma94PinchedQuadrilateralStatement

namespace OsinLemma94ClassPolygons

variable {G : Type u} [Group G] {Lambda : Type w}
  {W : Set (List (RelLetter G Lambda))}
  {D : RelGenSet G Lambda} {lambda c : ℝ} {eps : ℕ}
  {Delta : DiscDiagram.{u, w, v} W}
  {cuts : SectionCuts D lambda c Delta.boundaryWord}
  {S : GloballyDistinguishedSectionFamily D lambda c eps Delta cuts}
  {P : OsinLemma94RealizedPolygons S}

/-- The pieces of class `i` of polygon `k`: each side of the class with the gap after it. -/
def pinchedPieces (Q : OsinLemma94ClassPolygons P) (k : Fin P.count) (i : ℕ) :
    List (List S.diagram.toCombMap.Dart × List S.diagram.toCombMap.Dart) :=
  (Q.classSides k i).map fun s => (P.sideDarts k s, Q.gap k s)

/-- The pieces of a class, read with their gaps, are the darts of the class. -/
theorem flatMap_pinchedPieces (Q : OsinLemma94ClassPolygons P) (k : Fin P.count) (i : ℕ) :
    ((Q.pinchedPieces k i).flatMap fun p => p.1 ++ p.2) = Q.classDarts k i := by
  simp only [pinchedPieces, classDarts, List.flatMap_map]

/-- The sides of the pieces of a class are the sides of the class. -/
theorem flatMap_fst_pinchedPieces (Q : OsinLemma94ClassPolygons P) (k : Fin P.count) (i : ℕ) :
    (Q.pinchedPieces k i).flatMap Prod.fst = (Q.classSides k i).flatMap (P.sideDarts k) := by
  simp only [pinchedPieces, List.flatMap_map]

/-- Every side of a piece of a class is nonempty, and every gap reads the identity. -/
theorem pinchedPieces_spec (Q : OsinLemma94ClassPolygons P) {k : Fin P.count} {i : ℕ}
    (hi : i < Q.classCount k)
    {p : List S.diagram.toCombMap.Dart × List S.diagram.toCombMap.Dart}
    (hp : p ∈ Q.pinchedPieces k i) :
    p.1 ≠ [] ∧ RelLetter.listVal (dartWord S.diagram p.2) = 1 := by
  simp only [pinchedPieces, List.mem_map] at hp
  obtain ⟨s, hs, rfl⟩ := hp
  have hside : s < P.sideCount k := by
    have hmem : s ∈ (List.range (Q.classCount k)).flatMap (Q.classSides k) :=
      List.mem_flatMap.mpr ⟨i, List.mem_range.mpr hi, hs⟩
    rw [Q.sides_eq k, List.mem_rotate, List.mem_range] at hmem
    exact hmem
  exact ⟨P.side_ne_nil k s hside, Q.gap_value k i hi s hs⟩

/-- The last piece of a class has no gap. -/
theorem pinchedPieces_getLast? (Q : OsinLemma94ClassPolygons P) {k : Fin P.count} {i : ℕ}
    (hi : i < Q.classCount k)
    {p : List S.diagram.toCombMap.Dart × List S.diagram.toCombMap.Dart}
    (hp : p ∈ (Q.pinchedPieces k i).getLast?) : p.2 = [] := by
  simp only [pinchedPieces, List.getLast?_map, Option.mem_def, Option.map_eq_some_iff] at hp
  obtain ⟨s, hs, rfl⟩ := hp
  exact Q.gap_last k i hi s (Option.mem_def.mpr hs)

/-- **A class of kind `cell j` as pieces.**  The pieces of the class read one arc of the `j`-th
relator cell from across. -/
theorem exists_cellArc_pinchedPieces (Q : OsinLemma94ClassPolygons P) {k : Fin P.count}
    {i : ℕ} {j : Fin S.diagram.rCellCount} (hi : i < Q.classCount k)
    (hkind : Q.classKind k i = .cell j) :
    ∃ arc : CyclicArc (cellDarts S.diagram j),
      arc.reverseDarts = (Q.pinchedPieces k i).flatMap fun p => p.1 ++ p.2 := by
  obtain ⟨arc, harc⟩ := Q.cell_arc k i j hi hkind
  exact ⟨arc, harc.symm.trans (Q.flatMap_pinchedPieces k i).symm⟩

/-- **A class of kind `boundary j` as pieces.**  The pieces of the class read one arc of `∂Δ`
inside section `j`. -/
theorem exists_boundaryArc_pinchedPieces (Q : OsinLemma94ClassPolygons P) {k : Fin P.count}
    {i j : ℕ} (hi : i < Q.classCount k) (hkind : Q.classKind k i = .boundary j) :
    ∃ hj : j < cuts.count, ∃ arc : CyclicArc (targetDarts S.diagram none),
      targetBoundaryDarts S.diagram none arc =
          (Q.pinchedPieces k i).flatMap (fun p => p.1 ++ p.2) ∧
        cuts.cut ⟨j, by omega⟩ ≤ arc.start.1 ∧
          arc.start.1 + arc.length ≤ cuts.cut ⟨j + 1, by omega⟩ := by
  obtain ⟨hj, arc, harc, h1, h2⟩ := Q.boundary_arc k i j hi hkind
  exact ⟨hj, arc, harc.symm.trans (Q.flatMap_pinchedPieces k i).symm, h1, h2⟩

end OsinLemma94ClassPolygons

end GroupApproximation.GGT.VanKampen

#audit_axioms GroupApproximation.GGT.VanKampen.Embedded.reverseDarts_ne_nil_of_length_pos
#audit_axioms GroupApproximation.GGT.VanKampen.Embedded.targetBoundaryDarts_ne_nil_of_length_pos
#audit_axioms
  GroupApproximation.GGT.VanKampen.OsinLemma94PinchedQuadrilateralStatement.false_of_quadrilateral
#audit_axioms GroupApproximation.GGT.VanKampen.OsinLemma94ClassPolygons.flatMap_pinchedPieces
#audit_axioms GroupApproximation.GGT.VanKampen.OsinLemma94ClassPolygons.flatMap_fst_pinchedPieces
#audit_axioms GroupApproximation.GGT.VanKampen.OsinLemma94ClassPolygons.pinchedPieces_spec
#audit_axioms GroupApproximation.GGT.VanKampen.OsinLemma94ClassPolygons.pinchedPieces_getLast?
#audit_axioms
  GroupApproximation.GGT.VanKampen.OsinLemma94ClassPolygons.exists_cellArc_pinchedPieces
#audit_axioms
  GroupApproximation.GGT.VanKampen.OsinLemma94ClassPolygons.exists_boundaryArc_pinchedPieces
