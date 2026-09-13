import GroupApproximation.GGT.VanKampen.Estimating.OsinPocketCellWalkChain
import GroupApproximation.GGT.VanKampen.Estimating.OsinPocketCopyWalk
import GroupApproximation.GGT.VanKampen.Estimating.OsinAppendixO52Collapse
import GroupApproximation.GGT.VanKampen.Estimating.OsinAppendixSectionMultipleEdge
import GroupApproximation.Meta.AxiomGuard

/-!
# Duplicate-free cell pocket walks under edge conditions

Osin, arXiv:math/0411039v3, §9, proof of Lemma 9.7(b): two distinct selected regions joining the
same two distinct cells `Π_i` and `Π_j` bound a subdiagram `Γ_1` with
`∂Γ_1 = s_1 t_1 s_2 t_2`, where `s_1`, `s_2` are sides of the two regions and `t_1`, `t_2` are
arcs of `Π_i` and `Π_j`.

The walk `CellPocketWalk.walk` of two regions `a`, `b` joining `i` and `j` has four parts: the side
of `b` leaving `Π_j`, an arc of `Π_i` read backwards, the side of `a` leaving `Π_i`, and an arc of
`Π_j` read backwards.  A dart of a side has its face in its region and the face across it outside;
a dart of the first arc has `Π_i` across it, and a dart of the second arc has `Π_j` across it.  This
module is the cell-to-cell analogue of `PocketWalk.CopyClean` (`OsinPocketCopyWalk`): under edge
conditions separating these faces, the walk has no repeated dart and no dart together with its
reverse.

* `CellPocketWalk.CopyClean a b i j`: the edge conditions.  No edge has `Π_i` on both sides, no
  edge has `Π_j` on both sides, no edge joins `Π_i` to `Π_j`, no edge joins a face of `a` to a face
  of `b`, and no side dart has `Π_i` or `Π_j` across it.
* `CellPocketWalk.walk_nodup_of_copyClean`: the walk has no repeated dart.  Distinct cells have
  distinct faces (`Embedded.cell_face_ne`), so the two arcs share no dart.
* `CellPocketWalk.alpha_not_mem_walk_of_copyClean`: at least area, no dart of the walk has its
  reverse in the walk.  A region at least area contains no relator cell
  (`ContiguityGeometry.innerGRegion`).
* `CellPocketWalk.walk_nodup_and_alpha_not_mem`: both conclusions.
* `CellPocketWalk.exists_of_joinsCells_clean`: the walk of `exists_of_joinsCells` is a nonempty
  closed walk, and under the edge conditions at least area it is duplicate-free and uses no edge in
  both directions.
* `CellPocketCopyCleanStatement`: a globally distinguished family with two distinct regions joining
  the same two distinct cells has a globally distinguished family over the same diagram and cuts
  with such a pair satisfying the edge conditions.  Stated here, not proved.  The expected
  producer is edge doubling (`SurgeryFaceEdgeDoubling`) along the offending edges, as in
  `OuterSpurThickeningStatement`.
* `CellPocketWalk.exists_clean_of_copy`: the walk data on the copy, from that statement.

## Manuscript status

Infrastructure for `thm:hull` (tex 2121,
`\begin{theorem}[Hull's small cancellation theorem]\label{thm:hull}`), through Osin's Lemma 9.7(b);
certifies no printed sentence on its own.
-/

namespace GroupApproximation.GGT.VanKampen

universe u w v

open Embedded HullSC WordMetric

section Diagram

variable {G : Type u} [Group G] {Lambda : Type w} {W : Set (List (RelLetter G Lambda))}
  {D : RelGenSet G Lambda} {eps : ℕ} {X : DiscDiagram.{u, w, v} W}

namespace Embedded.RegionCandidate

/-- A dart of the side of a region leaving a cell has its face in the region and the face across
it outside. -/
theorem mem_sideFrom_boundary (z : RegionCandidate D eps X) (k : Fin X.rCellCount)
    {d : X.toCombMap.Dart} (hd : d ∈ z.sideFrom k) :
    X.toCombMap.faceOf d ∈ z.1 ∧ X.toCombMap.faceOf (X.toCombMap.alpha d) ∉ z.1 := by
  by_cases hs : z.2.source = k
  · rw [sideFrom, if_pos hs] at hd
    exact PocketWalk.mem_rightSide_boundary z hd
  · rw [sideFrom, if_neg hs] at hd
    exact PocketWalk.mem_leftSide_boundary z hd

/-- The side of a region leaving a cell has no repeated dart. -/
theorem sideFrom_nodup (z : RegionCandidate D eps X) (k : Fin X.rCellCount) :
    (z.sideFrom k).Nodup := by
  by_cases hs : z.2.source = k
  · rw [sideFrom, if_pos hs]
    exact z.2.rightSide_nodup
  · rw [sideFrom, if_neg hs]
    exact z.2.leftSide_nodup

end Embedded.RegionCandidate

namespace CellPocketWalk

/-- **The edge conditions for the cell pocket walk of `a` and `b` between `Π_i` and `Π_j`.**  No
edge has `Π_i` on both sides, no edge has `Π_j` on both sides, no edge joins `Π_j` to `Π_i`, no
edge joins a face of `a` to a face of `b`, and no dart of the side of `b` leaving `Π_j` or of the
side of `a` leaving `Π_i` has `Π_i` or `Π_j` across it. -/
structure CopyClean (a b : RegionCandidate D eps X) (i j : Fin X.rCellCount) : Prop where
  cell_self_first : ∀ d, X.toCombMap.faceOf d = (cell X i).face →
    X.toCombMap.faceOf (X.toCombMap.alpha d) ≠ (cell X i).face
  cell_self_second : ∀ d, X.toCombMap.faceOf d = (cell X j).face →
    X.toCombMap.faceOf (X.toCombMap.alpha d) ≠ (cell X j).face
  cell_cell : ∀ d, X.toCombMap.faceOf d = (cell X j).face →
    X.toCombMap.faceOf (X.toCombMap.alpha d) ≠ (cell X i).face
  regions : ∀ d, X.toCombMap.faceOf d ∈ a.1 → X.toCombMap.faceOf (X.toCombMap.alpha d) ∉ b.1
  side_first : ∀ d ∈ b.sideFrom j ++ a.sideFrom i,
    X.toCombMap.faceOf (X.toCombMap.alpha d) ≠ (cell X i).face
  side_second : ∀ d ∈ b.sideFrom j ++ a.sideFrom i,
    X.toCombMap.faceOf (X.toCombMap.alpha d) ≠ (cell X j).face

/-- A dart of an arc of a relator cell read backwards has that cell across it. -/
theorem faceOf_alpha_of_mem_invDarts_arc {k : Fin X.rCellCount} (A : CyclicArc (cellDarts X k))
    {d : X.toCombMap.Dart} (hd : d ∈ invDarts X A.darts) :
    X.toCombMap.faceOf (X.toCombMap.alpha d) = (cell X k).face := by
  obtain ⟨e, he, rfl⟩ := List.mem_map.mp hd
  rw [X.toCombMap.alpha_involutive e]
  exact ((X.faceBoundary (cell X k).face).mem_iff e).mp
    (A.mem_cycle_of_mem_darts (List.mem_reverse.mp he))

variable {i j : Fin X.rCellCount}

/-- A dart of the cell pocket walk lies in one of its four parts. -/
theorem mem_walk_cases (K : CellPocketWalk D eps X i j) {d : X.toCombMap.Dart}
    (hd : d ∈ K.walk) :
    d ∈ K.firstSide ∨ d ∈ invDarts X K.firstArc.darts ∨ d ∈ K.secondSide ∨
      d ∈ invDarts X K.secondArc.darts := by
  simp only [CellPocketWalk.walk, List.mem_append] at hd
  rcases hd with ((hd | hd) | hd) | hd
  · exact Or.inl hd
  · exact Or.inr (Or.inl hd)
  · exact Or.inr (Or.inr (Or.inl hd))
  · exact Or.inr (Or.inr (Or.inr hd))

/-- **The cell pocket walk has no repeated dart.**  Each part has none; the sides lie in disjoint
regions, no side dart has `Π_i` or `Π_j` across it, and the two arcs have the distinct cells
`Π_i` and `Π_j` across them. -/
theorem walk_nodup_of_copyClean (K : CellPocketWalk D eps X i j)
    {a b : RegionCandidate D eps X} (hij : i ≠ j) (hfirst : K.firstSide = b.sideFrom j)
    (hsecond : K.secondSide = a.sideFrom i) (hab : Disjoint a.1 b.1)
    (hclean : CopyClean a b i j) : K.walk.Nodup := by
  have hleft : ∀ d ∈ K.firstSide, X.toCombMap.faceOf d ∈ b.1 := fun d hd =>
    (b.mem_sideFrom_boundary j (by rwa [hfirst] at hd)).1
  have hright : ∀ d ∈ K.secondSide, X.toCombMap.faceOf d ∈ a.1 := fun d hd =>
    (a.mem_sideFrom_boundary i (by rwa [hsecond] at hd)).1
  have hsideFirst : ∀ d ∈ K.firstSide ++ K.secondSide,
      X.toCombMap.faceOf (X.toCombMap.alpha d) ≠ (cell X i).face := by
    rw [hfirst, hsecond]
    exact hclean.side_first
  have hsideSecond : ∀ d ∈ K.firstSide ++ K.secondSide,
      X.toCombMap.faceOf (X.toCombMap.alpha d) ≠ (cell X j).face := by
    rw [hfirst, hsecond]
    exact hclean.side_second
  show (K.firstSide ++ invDarts X K.firstArc.darts ++ K.secondSide ++
    invDarts X K.secondArc.darts).Nodup
  refine PocketWalk.nodup_append_four ?_
    ((List.nodup_reverse.mpr (K.firstArc.darts_nodup (cellDarts_nodup X i))).map
      X.toCombMap.alpha_involutive.injective)
    ?_
    ((List.nodup_reverse.mpr (K.secondArc.darts_nodup (cellDarts_nodup X j))).map
      X.toCombMap.alpha_involutive.injective) ?_ ?_ ?_ ?_ ?_ ?_
  · rw [hfirst]
    exact b.sideFrom_nodup j
  · rw [hsecond]
    exact a.sideFrom_nodup i
  · intro d hd h2
    exact hsideFirst d (List.mem_append.mpr (Or.inl hd))
      (faceOf_alpha_of_mem_invDarts_arc K.firstArc h2)
  · intro d hd h3
    exact Finset.disjoint_left.mp hab (hright d h3) (hleft d hd)
  · intro d hd h4
    exact hsideSecond d (List.mem_append.mpr (Or.inl hd))
      (faceOf_alpha_of_mem_invDarts_arc K.secondArc h4)
  · intro d h2 h3
    exact hsideFirst d (List.mem_append.mpr (Or.inr h3))
      (faceOf_alpha_of_mem_invDarts_arc K.firstArc h2)
  · intro d h2 h4
    exact Embedded.cell_face_ne hij
      ((faceOf_alpha_of_mem_invDarts_arc K.firstArc h2).symm.trans
        (faceOf_alpha_of_mem_invDarts_arc K.secondArc h4))
  · intro d h3 h4
    exact hsideSecond d (List.mem_append.mpr (Or.inr h3))
      (faceOf_alpha_of_mem_invDarts_arc K.secondArc h4)

/-- **No dart of the cell pocket walk has its reverse in the walk.**  A side dart has its region
across its reverse; the regions at least area avoid both cells and have no edge between them.  The
remaining pairs are the edges excluded by `CopyClean`. -/
theorem alpha_not_mem_walk_of_copyClean (hlea : X.LeastArea) (K : CellPocketWalk D eps X i j)
    {a b : RegionCandidate D eps X} (hfirst : K.firstSide = b.sideFrom j)
    (hsecond : K.secondSide = a.sideFrom i) (hclean : CopyClean a b i j) :
    ∀ d ∈ K.walk, X.toCombMap.alpha d ∉ K.walk := by
  have hinv : ∀ d : X.toCombMap.Dart, X.toCombMap.alpha (X.toCombMap.alpha d) = d :=
    X.toCombMap.alpha_involutive
  have p1 : ∀ d ∈ K.firstSide, X.toCombMap.faceOf d ∈ b.1 ∧
      X.toCombMap.faceOf (X.toCombMap.alpha d) ∉ b.1 := fun d hd =>
    b.mem_sideFrom_boundary j (by rwa [hfirst] at hd)
  have p3 : ∀ d ∈ K.secondSide, X.toCombMap.faceOf d ∈ a.1 ∧
      X.toCombMap.faceOf (X.toCombMap.alpha d) ∉ a.1 := fun d hd =>
    a.mem_sideFrom_boundary i (by rwa [hsecond] at hd)
  have p2 : ∀ d ∈ invDarts X K.firstArc.darts,
      X.toCombMap.faceOf (X.toCombMap.alpha d) = (cell X i).face := fun d hd =>
    faceOf_alpha_of_mem_invDarts_arc K.firstArc hd
  have p4 : ∀ d ∈ invDarts X K.secondArc.darts,
      X.toCombMap.faceOf (X.toCombMap.alpha d) = (cell X j).face := fun d hd =>
    faceOf_alpha_of_mem_invDarts_arc K.secondArc hd
  have avoid : ∀ (z : RegionCandidate D eps X) (k : Fin X.rCellCount), (cell X k).face ∉ z.1 :=
    fun z k => (z.2.innerGRegion hlea).cells_avoid (cell X k) (cell_mem X k)
  intro d hd had
  rcases K.mem_walk_cases hd with h | h | h | h <;>
    rcases K.mem_walk_cases had with g | g | g | g
  · exact (p1 d h).2 (p1 _ g).1
  · have e := p2 _ g
    rw [hinv] at e
    exact avoid b i (by rw [← e]; exact (p1 d h).1)
  · have e := hclean.regions _ (p3 _ g).1
    rw [hinv] at e
    exact e (p1 d h).1
  · have e := p4 _ g
    rw [hinv] at e
    exact avoid b j (by rw [← e]; exact (p1 d h).1)
  · exact avoid b i (by rw [← p2 d h]; exact (p1 _ g).1)
  · have e := p2 _ g
    rw [hinv] at e
    exact hclean.cell_self_first d e (p2 d h)
  · exact avoid a i (by rw [← p2 d h]; exact (p3 _ g).1)
  · have e := p4 _ g
    rw [hinv] at e
    exact hclean.cell_cell d e (p2 d h)
  · exact hclean.regions d (p3 d h).1 (p1 _ g).1
  · have e := p2 _ g
    rw [hinv] at e
    exact avoid a i (by rw [← e]; exact (p3 d h).1)
  · exact (p3 d h).2 (p3 _ g).1
  · have e := p4 _ g
    rw [hinv] at e
    exact avoid a j (by rw [← e]; exact (p3 d h).1)
  · exact avoid b j (by rw [← p4 d h]; exact (p1 _ g).1)
  · have e := p2 _ g
    rw [hinv] at e
    have e' := hclean.cell_cell _ (p4 d h)
    rw [hinv] at e'
    exact e' e
  · exact avoid a j (by rw [← p4 d h]; exact (p3 _ g).1)
  · have e := p4 _ g
    rw [hinv] at e
    exact hclean.cell_self_second d e (p4 d h)

/-- **Step 3 of the cell pocket.**  At least area, the cell pocket walk of two disjoint regions
under the edge conditions has no repeated dart and no dart with its reverse. -/
theorem walk_nodup_and_alpha_not_mem (hlea : X.LeastArea) (K : CellPocketWalk D eps X i j)
    {a b : RegionCandidate D eps X} (hij : i ≠ j) (hfirst : K.firstSide = b.sideFrom j)
    (hsecond : K.secondSide = a.sideFrom i) (hab : Disjoint a.1 b.1)
    (hclean : CopyClean a b i j) :
    K.walk.Nodup ∧ ∀ d ∈ K.walk, X.toCombMap.alpha d ∉ K.walk :=
  ⟨K.walk_nodup_of_copyClean hij hfirst hsecond hab hclean,
    K.alpha_not_mem_walk_of_copyClean hlea hfirst hsecond hclean⟩

end CellPocketWalk

end Diagram

variable {G : Type u} [Group G] {Lambda : Type w} {W : Set (List (RelLetter G Lambda))}

/-- **A clean pair of regions joining two cells, on a copy** (not proved here).  A globally
distinguished family over a least-area diagram with two distinct regions joining the same two
distinct cells has a globally distinguished family over the same diagram and cuts with two distinct
regions joining two distinct cells that satisfy the edge conditions `CellPocketWalk.CopyClean`. -/
def CellPocketCopyCleanStatement : Prop :=
  ∀ {G : Type u} [Group G] {Lambda : Type w} (D : RelGenSet G Lambda) (lambda c : ℝ) (eps : ℕ)
    (W : Set (List (RelLetter G Lambda))) (Delta : DiscDiagram.{u, w, v} W)
    (cuts : SectionCuts D lambda c Delta.boundaryWord),
    Delta.LeastArea →
      ∀ S : GloballyDistinguishedSectionFamily D lambda c eps Delta cuts,
        ∀ a ∈ S.family, ∀ b ∈ S.family, a ≠ b → ∀ i j : Fin S.diagram.rCellCount, i ≠ j →
          a.JoinsCells i j → b.JoinsCells i j →
            ∃ (S' : GloballyDistinguishedSectionFamily D lambda c eps Delta cuts)
              (a' b' : RegionCandidate D eps S'.diagram) (i' j' : Fin S'.diagram.rCellCount),
              a' ∈ S'.family ∧ b' ∈ S'.family ∧ a' ≠ b' ∧ i' ≠ j' ∧
                a'.JoinsCells i' j' ∧ b'.JoinsCells i' j' ∧
                  CellPocketWalk.CopyClean a' b' i' j'

namespace CellPocketWalk

variable {D : RelGenSet G Lambda} {eps : ℕ} {Delta : DiscDiagram.{u, w, v} W} {lambda c : ℝ}
  {cuts : SectionCuts D lambda c Delta.boundaryWord}

/-- **The clean cell pocket walk of two regions joining two cells.**  The walk of
`exists_of_joinsCells` is a nonempty closed walk, and at least area under the edge conditions it
has no repeated dart and no dart with its reverse. -/
theorem exists_of_joinsCells_clean (S : RealizedSectionFamily D lambda c eps Delta cuts)
    {i j : Fin S.diagram.rCellCount} {a b : RegionCandidate D eps S.diagram}
    (ha : a ∈ S.family) (hb : b ∈ S.family) (hab : a ≠ b) (hij : i ≠ j)
    (hai : a.JoinsCells i j) (hbi : b.JoinsCells i j) :
    ∃ K : CellPocketWalk D eps S.diagram i j,
      K.firstSide = b.sideFrom j ∧ K.secondSide = a.sideFrom i ∧
        (∃ G₁ : CyclicArc (cellDarts S.diagram i),
          K.firstArc.darts = a.cellArcList i ++ G₁.darts ++ b.cellArcList i) ∧
        (∃ G₂ : CyclicArc (cellDarts S.diagram j),
          K.secondArc.darts = b.cellArcList j ++ G₂.darts ++ a.cellArcList j) ∧
        ∃ hne : K.walk ≠ [],
          (K.walk.IsChain fun d e => S.diagram.toCombMap.vertexOf
            (S.diagram.toCombMap.alpha d) = S.diagram.toCombMap.vertexOf e) ∧
          S.diagram.toCombMap.vertexOf (S.diagram.toCombMap.alpha (K.walk.getLast hne)) =
            S.diagram.toCombMap.vertexOf (K.walk.head hne) ∧
          (S.diagram.LeastArea → CopyClean a b i j →
            K.walk.Nodup ∧ ∀ d ∈ K.walk, S.diagram.toCombMap.alpha d ∉ K.walk) := by
  obtain ⟨K, hfirst, hsecond, hG₁, hG₂, hne, hchain, hcloses⟩ :=
    exists_of_joinsCells_closedWalk S ha hb hab hij hai hbi
  exact ⟨K, hfirst, hsecond, hG₁, hG₂, hne, hchain, hcloses, fun hlea hclean =>
    K.walk_nodup_and_alpha_not_mem hlea hij hfirst hsecond (S.pairwise a ha b hb hab) hclean⟩

/-- **Step 3 on the copy.**  From `CellPocketCopyCleanStatement`, two distinct regions joining the
same two distinct cells in a globally distinguished family over a least-area diagram give a
globally distinguished family over the same diagram and cuts, two regions joining two distinct
cells there, and their cell pocket walk: a nonempty closed walk with no repeated dart and no dart
with its reverse. -/
theorem exists_clean_of_copy (hcopy : CellPocketCopyCleanStatement.{u, w, v})
    (hlea : Delta.LeastArea) (S : GloballyDistinguishedSectionFamily D lambda c eps Delta cuts)
    {a b : RegionCandidate D eps S.diagram} (ha : a ∈ S.family) (hb : b ∈ S.family)
    (hab : a ≠ b) {i j : Fin S.diagram.rCellCount} (hij : i ≠ j) (hai : a.JoinsCells i j)
    (hbi : b.JoinsCells i j) :
    ∃ (S' : GloballyDistinguishedSectionFamily D lambda c eps Delta cuts)
      (a' b' : RegionCandidate D eps S'.diagram) (i' j' : Fin S'.diagram.rCellCount)
      (K : CellPocketWalk D eps S'.diagram i' j'),
      a' ∈ S'.family ∧ b' ∈ S'.family ∧ a' ≠ b' ∧ i' ≠ j' ∧
        a'.JoinsCells i' j' ∧ b'.JoinsCells i' j' ∧ CopyClean a' b' i' j' ∧
        K.firstSide = b'.sideFrom j' ∧ K.secondSide = a'.sideFrom i' ∧
        (∃ G₁ : CyclicArc (cellDarts S'.diagram i'),
          K.firstArc.darts = a'.cellArcList i' ++ G₁.darts ++ b'.cellArcList i') ∧
        (∃ G₂ : CyclicArc (cellDarts S'.diagram j'),
          K.secondArc.darts = b'.cellArcList j' ++ G₂.darts ++ a'.cellArcList j') ∧
        ∃ hne : K.walk ≠ [],
          (K.walk.IsChain fun d e => S'.diagram.toCombMap.vertexOf
            (S'.diagram.toCombMap.alpha d) = S'.diagram.toCombMap.vertexOf e) ∧
          S'.diagram.toCombMap.vertexOf (S'.diagram.toCombMap.alpha (K.walk.getLast hne)) =
            S'.diagram.toCombMap.vertexOf (K.walk.head hne) ∧
          K.walk.Nodup ∧ ∀ d ∈ K.walk, S'.diagram.toCombMap.alpha d ∉ K.walk := by
  obtain ⟨S', a', b', i', j', ha', hb', hab', hij', hai', hbi', hclean⟩ :=
    hcopy D lambda c eps W Delta cuts hlea S a ha b hb hab i j hij hai hbi
  obtain ⟨K, hfirst, hsecond, hG₁, hG₂, hne, hchain, hcloses⟩ :=
    exists_of_joinsCells_closedWalk S'.toRealizedSectionFamily ha' hb' hab' hij' hai' hbi'
  obtain ⟨hnodup, halpha⟩ := K.walk_nodup_and_alpha_not_mem (S'.equiv.leastArea hlea) hij'
    hfirst hsecond (S'.pairwise a' ha' b' hb' hab') hclean
  exact ⟨S', a', b', i', j', K, ha', hb', hab', hij', hai', hbi', hclean, hfirst, hsecond, hG₁,
    hG₂, hne, hchain, hcloses, hnodup, halpha⟩

end CellPocketWalk

end GroupApproximation.GGT.VanKampen

#audit_axioms GroupApproximation.GGT.VanKampen.Embedded.RegionCandidate.mem_sideFrom_boundary
#audit_axioms GroupApproximation.GGT.VanKampen.Embedded.RegionCandidate.sideFrom_nodup
#audit_axioms GroupApproximation.GGT.VanKampen.CellPocketWalk.faceOf_alpha_of_mem_invDarts_arc
#audit_axioms GroupApproximation.GGT.VanKampen.CellPocketWalk.mem_walk_cases
#audit_axioms GroupApproximation.GGT.VanKampen.CellPocketWalk.walk_nodup_of_copyClean
#audit_axioms GroupApproximation.GGT.VanKampen.CellPocketWalk.alpha_not_mem_walk_of_copyClean
#audit_axioms GroupApproximation.GGT.VanKampen.CellPocketWalk.walk_nodup_and_alpha_not_mem
#audit_axioms GroupApproximation.GGT.VanKampen.CellPocketCopyCleanStatement
#audit_axioms GroupApproximation.GGT.VanKampen.CellPocketWalk.exists_of_joinsCells_clean
#audit_axioms GroupApproximation.GGT.VanKampen.CellPocketWalk.exists_clean_of_copy
