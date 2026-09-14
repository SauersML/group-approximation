import GroupApproximation.GGT.VanKampen.Estimating.OsinPocketMultipleEdgeAssembly
import GroupApproximation.GGT.VanKampen.Estimating.OsinPocketCellFaceSet
import GroupApproximation.GGT.VanKampen.Estimating.OsinPocketCellCopyWalk
import GroupApproximation.GGT.VanKampen.Estimating.OsinPocketCellWalkColour
import GroupApproximation.Meta.AxiomGuard

/-!
# The multiple-edge pocket region on an O-equivalent copy

Osin, arXiv:math/0411039v3, §9, proof of Lemma 9.7(b): two distinct selected regions joining the
same two distinct cells bound a subdiagram `Γ_1` with `∂Γ_1 = s_1 t_1 s_2 t_2`, where `t_1` and
`t_2` are arcs of the two cells.  If `Γ_1` kept no relator cell, merging the two regions would
contradict the extremality of the family, "passing to an O-equivalent diagram if necessary".

`MultipleEdgePocketRegionInput` (`OsinPocketRegionSide`) asks for the pocket region on the optimal
diagram `S.diagram` itself.  In configuration (b′), a spur on the first cell between two arcs
longer than `2ε`, no pocket region of `S.diagram` has the required decomposition, and excluding
(b′) from an optimal family needs Lemma 9.7(b), the lemma being proved.  So that form is circular.
`MultipleEdgePocketRegionCopyInput` states the same region data on an O-equivalent copy of the
least-area diagram `Δ` with letter labels, where the spur can be thickened (ruling (B); the
statement follows hull-select's r1 drafts, which never landed).  The copy is of `Δ`, not of
`S.diagram`: a producer through the edge thickenings outputs another optimal family over `Δ`, whose
diagram carries no recorded equivalence to `S.diagram`.

* `MultipleEdgePocketRegionInput.copyInput`: the form on `S.diagram` gives the copy form, so the
  copy form asks for no more.
* `multipleEdgeCutInput_of_copyPieces`: the copy form, the collar and the cell transport give
  `MultipleEdgeCutInput`, through `nonempty_osinMultipleEdgeCut_of_pocketRegion`.
* `multipleEdgePocketRegionCopyInput_of_pinch`: the copy form from the binder-5 route.
  `CellPocketWalk.exists_clean_of_copy` gives a clean pair of regions and their cell pocket walk on
  another optimal family, `CellPocketWalkColour.walk_orient` orients the walk,
  `CellPocketWalk.exists_cellPocketFaceSet_closedWalk_of_orient` makes it a cell pocket face set in
  walk order, and `CellPocketFaceSet.copyRegion_of_pinch` gives the region data on a copy.  The
  named residuals are `CellPocketCopyCleanStatement`, `CellPocketWalkOuterOffSideStatement` (the
  exterior is off the side of the walk), `CellPocketWalkSideRelatorCellStatement` (a relator cell is
  on it) and `CellPocketPinchPosStatement`.
* `OsinMultipleEdgePocketRegionCopySectionStatement` and its producers, uniformly in the
  parameters, with the thresholds `ε ≥ ε₀` and then `ρ ≥ ρ₀` of `OsinMultipleEdgeCutSectionStatement`.
  The pinch producer takes `ε₀ = 1`, since the pinch needs `0 < ε`.

## Manuscript status

Infrastructure for `thm:hull` (Hull's small cancellation theorem, through Osin's Lemma 9.7(b));
certifies no printed sentence on its own.
-/

namespace GroupApproximation.GGT.VanKampen

universe u w v

open Embedded HullSC WordMetric

section CopyInput

variable {G : Type u} [Group G] {Lambda : Type w}

/-- **The multiple-edge pocket region on an O-equivalent copy.**  Two distinct selected regions
joining the distinct cells `i` and `j` of the optimal diagram give an O-equivalent copy `X` of the
least-area diagram `Δ` with letter labels, and a pocket region of `X` with a relator cell inside and
two cells outside.  The inverse of its complement cycle reads a side, a reversed arc of the first
cell, a side and a reversed arc of the second, the side values of word norm at most `ε`.  Both
cycles of the pocket follow the face-set boundary. -/
def MultipleEdgePocketRegionCopyInput (D : RelGenSet G Lambda) (lambda c : ℝ) (eps : ℕ)
    (W : Set (List (RelLetter G Lambda))) : Prop :=
  ∀ (Delta : DiscDiagram.{u, w, v} W) (cuts : SectionCuts D lambda c Delta.boundaryWord),
    Delta.LeastArea →
      ∀ S : GloballyDistinguishedSectionFamily D lambda c eps Delta cuts,
        ∀ a ∈ S.family, ∀ b ∈ S.family, a ≠ b → ∀ i j : Fin S.diagram.rCellCount, i ≠ j →
          a.JoinsCells i j → b.JoinsCells i j →
            ∃ X : DiscDiagram.{u, w, v} W, Nonempty (OEquivalentDiscDiagram Delta X) ∧
              (∀ d, (symmetricLabelAlphabet D).IsLetter (X.label d)) ∧
              ∃ (P : PocketRegion X) (C : RelatorCell X.toCombMap X.outerFace W)
                (i' j' : Fin X.rCellCount) (s₁ s₂ : List X.toCombMap.Dart)
                (A₁ : CyclicArc (cellDarts X i')) (A₂ : CyclicArc (cellDarts X j')),
                C ∈ X.relatorCells ∧ C.face ∈ P.faces ∧
                  (cell X i').face ∉ P.faces ∧ (cell X j').face ∉ P.faces ∧
                  invDarts X P.outer.cycle =
                    s₁ ++ invDarts X A₁.darts ++ s₂ ++ invDarts X A₂.darts ∧
                  wordNorm D.alphabet.carrier (RelLetter.listVal (dartWord X s₁)) ≤ eps ∧
                  wordNorm D.alphabet.carrier (RelLetter.listVal (dartWord X s₂)) ≤ eps ∧
                  P.inner.FollowsBoundary ∧ P.outer.FollowsBoundary

variable {W : Set (List (RelLetter G Lambda))}

/-- **The pocket region on the optimal diagram is one on a copy**: the copy `S.diagram`, through the
O-equivalence of the optimal family. -/
theorem MultipleEdgePocketRegionInput.copyInput {D : RelGenSet G Lambda} {lambda c : ℝ}
    {eps : ℕ} (h : MultipleEdgePocketRegionInput.{u, w, v} D lambda c eps W) :
    MultipleEdgePocketRegionCopyInput.{u, w, v} D lambda c eps W := by
  intro Delta cuts hlea S a ha b hb hab i j hij hai hbi
  obtain ⟨P, C, s₁, s₂, A₁, A₂, hC, hCf, hi, hj, hdecomposition, -, -, hnorm₁, hnorm₂, hin,
      hout⟩ := h Delta cuts hlea S a ha b hb hab i j hij hai hbi
  exact ⟨S.diagram, ⟨S.equiv⟩, fun d => S.label_admissible d,
    P, C, i, j, s₁, s₂, A₁, A₂, hC, hCf, hi, hj, hdecomposition, hnorm₁, hnorm₂, hin, hout⟩

/-- **G2, multiple edges, from the pocket pieces on a copy.**  The collar and the cell transport run
on the copy, which is O-equivalent to the least-area diagram. -/
theorem multipleEdgeCutInput_of_copyPieces (hcollar : GeodesicCollarStatement.{u, w, v})
    (hcell : PocketCellTransportStatement.{u, w, v})
    {D : RelGenSet G Lambda} {eps rho : ℕ} {mu lambda c : ℝ}
    (hcondition : OsinCCondition D W eps mu lambda c rho) (hlambda : lambda ≤ 1) (hc : 0 ≤ c)
    (hpocket : MultipleEdgePocketRegionCopyInput.{u, w, v} D lambda c eps W) :
    MultipleEdgeCutInput.{u, w, v} D lambda c eps W := by
  intro Delta cuts hlea S a ha b hb hab i j hij hai hbi
  obtain ⟨X, ⟨E⟩, hlabel, P, C, i', j', s₁, s₂, A₁, A₂, hC, hCf, hi, hj, hdecomposition,
      hnorm₁, hnorm₂, hin, hout⟩ := hpocket Delta cuts hlea S a ha b hb hab i j hij hai hbi
  exact nonempty_osinMultipleEdgeCut_of_pocketRegion hcollar hcell hcondition hlambda hc hlea
    E hlabel P hin hout hC hCf hi hj A₁ A₂ s₁ s₂ hdecomposition hnorm₁ hnorm₂

end CopyInput

/-! ## The residuals of the binder-5 route -/

/-- **The exterior is off the side of the cell pocket walk** (named residual of binder 5).  Let `a`,
`b` be distinct regions of an optimal family over a least-area diagram, joining the distinct cells
`i` and `j` under the edge conditions, and let `K` be their cell pocket walk, a nonempty closed walk
with no repeated dart and no dart with its reverse.  Then the exterior face is not on the side of the
walk. -/
def CellPocketWalkOuterOffSideStatement : Prop :=
  ∀ {G : Type u} [Group G] {Lambda : Type w} {W : Set (List (RelLetter G Lambda))}
    {D : RelGenSet G Lambda} {eps : ℕ} {lambda c : ℝ} {Delta : DiscDiagram.{u, w, v} W}
    {cuts : SectionCuts D lambda c Delta.boundaryWord},
    Delta.LeastArea →
      ∀ (S : GloballyDistinguishedSectionFamily D lambda c eps Delta cuts)
        {i j : Fin S.diagram.rCellCount} {a b : RegionCandidate D eps S.diagram},
        a ∈ S.family → b ∈ S.family → a ≠ b → i ≠ j → a.JoinsCells i j → b.JoinsCells i j →
          CellPocketWalk.CopyClean a b i j →
          ∀ K : CellPocketWalk D eps S.diagram i j,
            K.firstSide = b.sideFrom j → K.secondSide = a.sideFrom i →
            (∃ G₁ : CyclicArc (cellDarts S.diagram i),
              K.firstArc.darts = a.cellArcList i ++ G₁.darts ++ b.cellArcList i) →
            (∃ G₂ : CyclicArc (cellDarts S.diagram j),
              K.secondArc.darts = b.cellArcList j ++ G₂.darts ++ a.cellArcList j) →
            ∀ hne : K.walk ≠ [],
              (K.walk.IsChain fun d e => S.diagram.toCombMap.vertexOf
                (S.diagram.toCombMap.alpha d) = S.diagram.toCombMap.vertexOf e) →
              S.diagram.toCombMap.vertexOf (S.diagram.toCombMap.alpha (K.walk.getLast hne)) =
                S.diagram.toCombMap.vertexOf (K.walk.head hne) →
              K.walk.Nodup → (∀ d ∈ K.walk, S.diagram.toCombMap.alpha d ∉ K.walk) →
                S.diagram.outerFace ∉ SimpleClosedWalkSides.sideFaces S.diagram.toCombMap K.walk

/-- **A relator cell is on the side of the cell pocket walk** (named residual of binder 5), with the
data of `CellPocketWalkOuterOffSideStatement`. -/
def CellPocketWalkSideRelatorCellStatement : Prop :=
  ∀ {G : Type u} [Group G] {Lambda : Type w} {W : Set (List (RelLetter G Lambda))}
    {D : RelGenSet G Lambda} {eps : ℕ} {lambda c : ℝ} {Delta : DiscDiagram.{u, w, v} W}
    {cuts : SectionCuts D lambda c Delta.boundaryWord},
    Delta.LeastArea →
      ∀ (S : GloballyDistinguishedSectionFamily D lambda c eps Delta cuts)
        {i j : Fin S.diagram.rCellCount} {a b : RegionCandidate D eps S.diagram},
        a ∈ S.family → b ∈ S.family → a ≠ b → i ≠ j → a.JoinsCells i j → b.JoinsCells i j →
          CellPocketWalk.CopyClean a b i j →
          ∀ K : CellPocketWalk D eps S.diagram i j,
            K.firstSide = b.sideFrom j → K.secondSide = a.sideFrom i →
            (∃ G₁ : CyclicArc (cellDarts S.diagram i),
              K.firstArc.darts = a.cellArcList i ++ G₁.darts ++ b.cellArcList i) →
            (∃ G₂ : CyclicArc (cellDarts S.diagram j),
              K.secondArc.darts = b.cellArcList j ++ G₂.darts ++ a.cellArcList j) →
            ∀ hne : K.walk ≠ [],
              (K.walk.IsChain fun d e => S.diagram.toCombMap.vertexOf
                (S.diagram.toCombMap.alpha d) = S.diagram.toCombMap.vertexOf e) →
              S.diagram.toCombMap.vertexOf (S.diagram.toCombMap.alpha (K.walk.getLast hne)) =
                S.diagram.toCombMap.vertexOf (K.walk.head hne) →
              K.walk.Nodup → (∀ d ∈ K.walk, S.diagram.toCombMap.alpha d ∉ K.walk) →
                ∃ kept : Fin S.diagram.rCellCount,
                  (cell S.diagram kept).face ∈
                    SimpleClosedWalkSides.sideFaces S.diagram.toCombMap K.walk

section SomeOrder

variable {G : Type u} [Group G] {Lambda : Type w} {W : Set (List (RelLetter G Lambda))}
  {D : RelGenSet G Lambda} {eps : ℕ} {lambda c : ℝ} {Delta : DiscDiagram.{u, w, v} W}
  {cuts : SectionCuts D lambda c Delta.boundaryWord}

/-- **The clean cell pocket walk of the pair in the order `(a, b)` between `Π_i` and `Π_j`, with the
exterior off its side.**  A predicate on the pair, in one chosen order, that the walk of
`CellPocketWalk.exists_of_joinsCells` for that order is a nonempty closed walk with no repeated dart
and no dart with its reverse, satisfying the cell edge conditions, whose side does not hold the
exterior. -/
def OuterOffSideForOrder (S : GloballyDistinguishedSectionFamily D lambda c eps Delta cuts)
    (a b : RegionCandidate D eps S.diagram) (i j : Fin S.diagram.rCellCount) : Prop :=
  CellPocketWalk.CopyClean a b i j →
    ∀ K : CellPocketWalk D eps S.diagram i j,
      K.firstSide = b.sideFrom j → K.secondSide = a.sideFrom i →
      (∃ G₁ : CyclicArc (cellDarts S.diagram i),
        K.firstArc.darts = a.cellArcList i ++ G₁.darts ++ b.cellArcList i) →
      (∃ G₂ : CyclicArc (cellDarts S.diagram j),
        K.secondArc.darts = b.cellArcList j ++ G₂.darts ++ a.cellArcList j) →
      ∀ hne : K.walk ≠ [],
        (K.walk.IsChain fun d e => S.diagram.toCombMap.vertexOf
          (S.diagram.toCombMap.alpha d) = S.diagram.toCombMap.vertexOf e) →
        S.diagram.toCombMap.vertexOf (S.diagram.toCombMap.alpha (K.walk.getLast hne)) =
          S.diagram.toCombMap.vertexOf (K.walk.head hne) →
        K.walk.Nodup → (∀ d ∈ K.walk, S.diagram.toCombMap.alpha d ∉ K.walk) →
          S.diagram.outerFace ∉ SimpleClosedWalkSides.sideFaces S.diagram.toCombMap K.walk

/-- **A relator cell on the side of the clean cell pocket walk of the pair in the order `(a, b)`.**
The same data as `OuterOffSideForOrder`, concluding that a relator cell is on the side. -/
def SideRelatorCellForOrder (S : GloballyDistinguishedSectionFamily D lambda c eps Delta cuts)
    (a b : RegionCandidate D eps S.diagram) (i j : Fin S.diagram.rCellCount) : Prop :=
  CellPocketWalk.CopyClean a b i j →
    ∀ K : CellPocketWalk D eps S.diagram i j,
      K.firstSide = b.sideFrom j → K.secondSide = a.sideFrom i →
      (∃ G₁ : CyclicArc (cellDarts S.diagram i),
        K.firstArc.darts = a.cellArcList i ++ G₁.darts ++ b.cellArcList i) →
      (∃ G₂ : CyclicArc (cellDarts S.diagram j),
        K.secondArc.darts = b.cellArcList j ++ G₂.darts ++ a.cellArcList j) →
      ∀ hne : K.walk ≠ [],
        (K.walk.IsChain fun d e => S.diagram.toCombMap.vertexOf
          (S.diagram.toCombMap.alpha d) = S.diagram.toCombMap.vertexOf e) →
        S.diagram.toCombMap.vertexOf (S.diagram.toCombMap.alpha (K.walk.getLast hne)) =
          S.diagram.toCombMap.vertexOf (K.walk.head hne) →
        K.walk.Nodup → (∀ d ∈ K.walk, S.diagram.toCombMap.alpha d ∉ K.walk) →
          ∃ kept : Fin S.diagram.rCellCount,
            (cell S.diagram kept).face ∈ SimpleClosedWalkSides.sideFaces S.diagram.toCombMap K.walk

/-- **The exterior is off the side of the cell pocket walk in SOME order** (respelled residual of
binder 5, owner `w1-binder-3`).  For a pair of distinct selected regions joining two distinct cells
of an optimal least-area family, the exterior face lies in at most one of the two complementary
pockets, so it is off the side of the walk of the order `(a, b, i, j)` or of the order `(b, a, j, i)`.
The fixed-order `CellPocketWalkOuterOffSideStatement` is over-strong; this is its correct form. -/
def CellPocketWalkOuterOffSideSomeOrderStatement : Prop :=
  ∀ {G : Type u} [Group G] {Lambda : Type w} {W : Set (List (RelLetter G Lambda))}
    {D : RelGenSet G Lambda} {eps : ℕ} {lambda c : ℝ} {Delta : DiscDiagram.{u, w, v} W}
    {cuts : SectionCuts D lambda c Delta.boundaryWord},
    Delta.LeastArea →
      ∀ (S : GloballyDistinguishedSectionFamily D lambda c eps Delta cuts)
        {i j : Fin S.diagram.rCellCount} {a b : RegionCandidate D eps S.diagram},
        a ∈ S.family → b ∈ S.family → a ≠ b → i ≠ j → a.JoinsCells i j → b.JoinsCells i j →
          OuterOffSideForOrder S a b i j ∨ OuterOffSideForOrder S b a j i

/-- **A relator cell is on the side of the cell pocket walk in BOTH orders** (respelled residual of
binder 5, owner `ms-inverses-2`).  The pocket between two cells always keeps a relator cell, in
either order, so this is not order-sensitive; stating it for both orders lets the assembly consume it
whichever order `CellPocketWalkOuterOffSideSomeOrderStatement` selects. -/
def CellPocketWalkSideRelatorCellBothOrdersStatement : Prop :=
  ∀ {G : Type u} [Group G] {Lambda : Type w} {W : Set (List (RelLetter G Lambda))}
    {D : RelGenSet G Lambda} {eps : ℕ} {lambda c : ℝ} {Delta : DiscDiagram.{u, w, v} W}
    {cuts : SectionCuts D lambda c Delta.boundaryWord},
    Delta.LeastArea →
      ∀ (S : GloballyDistinguishedSectionFamily D lambda c eps Delta cuts)
        {i j : Fin S.diagram.rCellCount} {a b : RegionCandidate D eps S.diagram},
        a ∈ S.family → b ∈ S.family → a ≠ b → i ≠ j → a.JoinsCells i j → b.JoinsCells i j →
          SideRelatorCellForOrder S a b i j ∧ SideRelatorCellForOrder S b a j i

end SomeOrder

section Pinch

variable {G : Type u} [Group G] {Lambda : Type w} {W : Set (List (RelLetter G Lambda))}

/-- **The multiple-edge pocket region on a copy, from the binder-5 route**, at `0 < ε`: the clean
pair on another optimal family (`CellPocketWalk.exists_clean_of_copy`), the orientation
(`CellPocketWalkColour.walk_orient`), the cell pocket face set in walk order
(`CellPocketWalk.exists_cellPocketFaceSet_closedWalk_of_orient`) and the pinch
(`CellPocketFaceSet.copyRegion_of_pinch`), composed with the O-equivalence of the other family. -/
theorem multipleEdgePocketRegionCopyInput_of_pinch
    (hcopy : CellPocketCopyCleanStatement.{u, w, v})
    (hout : CellPocketWalkOuterOffSideStatement.{u, w, v})
    (hkept : CellPocketWalkSideRelatorCellStatement.{u, w, v})
    (hpinch : CellPocketPinchPosStatement.{u, w, v})
    {D : RelGenSet G Lambda} {lambda c : ℝ} {eps : ℕ} (heps : 0 < eps) :
    MultipleEdgePocketRegionCopyInput.{u, w, v} D lambda c eps W := by
  intro Delta cuts hlea S a ha b hb hab i j hij hai hbi
  obtain ⟨S', a', b', i', j', K, ha', hb', hab', hij', hai', hbi', hclean, hfirst, hsecond, h₁, h₂,
      hne, hchain, hcloses, hnodup, halpha⟩ :=
    CellPocketWalk.exists_clean_of_copy hcopy hlea S ha hb hab hij hai hbi
  obtain ⟨F, -, hF⟩ := K.exists_cellPocketFaceSet_closedWalk_of_orient hne hnodup halpha hchain
    hcloses
    (fun _ hcol => CellPocketWalkColour.walk_orient S'.toRealizedSectionFamily ha' hb' hab' hai'
      hbi' K hfirst hsecond h₁ h₂ hcol)
    (hout hlea S' ha' hb' hab' hij' hai' hbi' hclean K hfirst hsecond h₁ h₂ hne hchain hcloses
      hnodup halpha)
    (hkept hlea S' ha' hb' hab' hij' hai' hbi' hclean K hfirst hsecond h₁ h₂ hne hchain hcloses
      hnodup halpha)
  obtain ⟨X, ⟨E⟩, hlabel, hrest⟩ :=
    CellPocketFaceSet.copyRegion_of_pinch hpinch heps (fun d => S'.label_admissible d) F hF
  exact ⟨X, ⟨S'.equiv.trans E⟩, hlabel, hrest⟩

end Pinch

/-! ## Uniformly in the parameters -/

/-- **The multiple-edge pocket region on a copy, uniformly in the parameters**, with the quantifier
prefix of `OsinMultipleEdgeCutSectionStatement`: `ε` at least a threshold `ε₀`, then `ρ` at least a
threshold `ρ₀`, for every family satisfying `C(ε, μ, λ, c, ρ)`. -/
def OsinMultipleEdgePocketRegionCopySectionStatement : Prop :=
  ∀ {G : Type u} [Group G] {Lambda : Type w} (D : RelGenSet G Lambda),
    (∃ delta : ℕ, Hyperbolic.IsFourPointHyperbolic D.alphabet.carrier delta) →
    ∀ lambda c mu : ℝ, 0 < lambda → lambda ≤ 1 → 0 ≤ c → 0 < mu → mu ≤ 1 / 16 →
      ∃ eps0 : ℕ, ∀ eps : ℕ, eps0 ≤ eps →
        ∃ rho0 : ℕ, 0 < rho0 ∧ ∀ rho : ℕ, rho0 ≤ rho →
          ∀ (W : Set (List (RelLetter G Lambda))),
            OsinCCondition D W eps mu lambda c rho →
              MultipleEdgePocketRegionCopyInput.{u, w, v} D lambda c eps W

/-- **The binder on the optimal diagram gives the binder on a copy**, with the same thresholds. -/
theorem OsinMultipleEdgePocketRegionSectionStatement.copySection
    (h : OsinMultipleEdgePocketRegionSectionStatement.{u, w, v}) :
    OsinMultipleEdgePocketRegionCopySectionStatement.{u, w, v} := by
  intro G _ Lambda D hhyp lambda c mu hlambda hlambda1 hc hmu hmu16
  obtain ⟨eps0, heps0⟩ := h D hhyp lambda c mu hlambda hlambda1 hc hmu hmu16
  refine ⟨eps0, fun eps heps => ?_⟩
  obtain ⟨rho0, hrho0, hrho⟩ := heps0 eps heps
  exact ⟨rho0, hrho0, fun rho hrho' W hcondition =>
    MultipleEdgePocketRegionInput.copyInput (hrho rho hrho' W hcondition)⟩

/-- **The binder on a copy from the binder-5 route**, with `ε₀ = 1` and `ρ₀ = 1`. -/
theorem osinMultipleEdgePocketRegionCopySection_of_pinch
    (hcopy : CellPocketCopyCleanStatement.{u, w, v})
    (hout : CellPocketWalkOuterOffSideStatement.{u, w, v})
    (hkept : CellPocketWalkSideRelatorCellStatement.{u, w, v})
    (hpinch : CellPocketPinchPosStatement.{u, w, v}) :
    OsinMultipleEdgePocketRegionCopySectionStatement.{u, w, v} := by
  intro _ _ _ _ _ _ _ _ _ _ _ _ _
  exact ⟨1, fun _ heps => ⟨1, Nat.one_pos, fun _ _ _ _ =>
    multipleEdgePocketRegionCopyInput_of_pinch hcopy hout hkept hpinch heps⟩⟩

/-- **G2, multiple edges, uniformly in the parameters, from the pocket pieces on a copy.**  The
thresholds are those of the copy producer. -/
theorem osinMultipleEdgeCutSection_of_copyPieces
    (hpocket : OsinMultipleEdgePocketRegionCopySectionStatement.{u, w, v})
    (hcollar : GeodesicCollarStatement.{u, w, v})
    (hcell : PocketCellTransportStatement.{u, w, v}) :
    OsinMultipleEdgeCutSectionStatement.{u, w, v} := by
  intro G _ Lambda D hhyp lambda c mu hlambda hlambda1 hc hmu hmu16
  obtain ⟨eps0, heps0⟩ := hpocket D hhyp lambda c mu hlambda hlambda1 hc hmu hmu16
  refine ⟨eps0, fun eps heps => ?_⟩
  obtain ⟨rho0, hrho0, hrho⟩ := heps0 eps heps
  exact ⟨rho0, hrho0, fun rho hrho' W hcondition =>
    multipleEdgeCutInput_of_copyPieces hcollar hcell hcondition hlambda1 hc
      (hrho rho hrho' W hcondition)⟩

end GroupApproximation.GGT.VanKampen

#audit_axioms GroupApproximation.GGT.VanKampen.MultipleEdgePocketRegionCopyInput
#audit_axioms GroupApproximation.GGT.VanKampen.MultipleEdgePocketRegionInput.copyInput
#audit_axioms GroupApproximation.GGT.VanKampen.multipleEdgeCutInput_of_copyPieces
#audit_axioms GroupApproximation.GGT.VanKampen.CellPocketWalkOuterOffSideStatement
#audit_axioms GroupApproximation.GGT.VanKampen.CellPocketWalkSideRelatorCellStatement
#audit_axioms GroupApproximation.GGT.VanKampen.OuterOffSideForOrder
#audit_axioms GroupApproximation.GGT.VanKampen.SideRelatorCellForOrder
#audit_axioms GroupApproximation.GGT.VanKampen.CellPocketWalkOuterOffSideSomeOrderStatement
#audit_axioms GroupApproximation.GGT.VanKampen.CellPocketWalkSideRelatorCellBothOrdersStatement
#audit_axioms GroupApproximation.GGT.VanKampen.multipleEdgePocketRegionCopyInput_of_pinch
#audit_axioms GroupApproximation.GGT.VanKampen.OsinMultipleEdgePocketRegionCopySectionStatement
#audit_axioms GroupApproximation.GGT.VanKampen.OsinMultipleEdgePocketRegionSectionStatement.copySection
#audit_axioms GroupApproximation.GGT.VanKampen.osinMultipleEdgePocketRegionCopySection_of_pinch
#audit_axioms GroupApproximation.GGT.VanKampen.osinMultipleEdgeCutSection_of_copyPieces
