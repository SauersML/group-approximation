import GroupApproximation.GGT.VanKampen.Estimating.Incidence
import GroupApproximation.GGT.VanKampen.Estimating.PieceCarrier
import GroupApproximation.GGT.VanKampen.FaceSetPeelProducer
import GroupApproximation.GGT.VanKampen.FaceShelling

/-!
# The local core of the Piece construction

`Embedded.CellPieceEquations` has exactly three fields, and this module
accounts for all three at one embedded region.

* `target` and `target_eq` are supplied by the caller; on a selected interior
  edge they are stored in `Embedded.InteriorEdge` itself, so the
  outer-boundary case never reaches this construction.
* `arcs_value` is the boundary-dart count.  With the boundary cycle in its
  stored decomposition
  `sourceArc.reverse ++ rightSide ++ targetBoundary ++ leftSide`, the equation
  `target = right⁻¹ * source * left⁻¹` is exactly the statement that the cycle
  has trivial value, which a complete face-deletion schedule produces.
  `Contiguity.targetBoundary_value_of_pasting` performs that conversion and
  `FaceSetBoundaryPeeling.to_homotopy` supplies the schedule, so the only input
  is vk's `Embedded.FaceSetEarStatement`: every single-cycle `G`-region has an
  ear.  Nothing else in the peel is open.
* `whole_ne` is the non-cancellation inequality.  It is the whole content of
  `Embedded.ReducedCellPieceBridge`: that structure's other four fields are a
  free repackaging, since `sourceWord` and `targetWord` may be taken to be the
  arc words themselves and `connector` is pinned by `connector_value_eq`.  So
  the bridge is not a smaller input than the inequality, and this module names
  the inequality directly as `EstimatingPieceNonCancellationStatement`.

`Embedded.cellPieceEquations_of_earStatement` is the resulting per-region
constructor; `Estimating/PieceConstruction.lean` specializes it along a
scaffold to close `EstimatingPieceConstructionStatement`.

**Source check (Osin, arXiv math/0411039, `embed-final.tex`).**  Lemma `O52`
is stated only for a contiguity of one cell to *another* cell: "for every
`e`-contiguity subdiagram `Gamma` of a cell `Pi` to another cell `Sigma`".  So
the self-contiguous case is excluded in the source, not handled by it.  The
non-cancellation step of Osin's proof is "If the third condition is not, then
`phi(s_1) phi(dPi) phi(s_1)^{-1} = phi(dSigma)` ... Hence we can cut the
subdiagram ... and fill the obtained hole with a diagram over (ZP) without
`R`-cells reducing the number of `R`-cells by 2.  This contradicts the
assumption that `Delta` is reduced."  Two things follow.  First, the excluded
identity is exactly `whole_ne` after unfolding the carrier words, so the
algebraic shape of `DiscDiagram.Reduced` is the right one.  Second, Osin's
"reduced" is *minimality of the `R`-cell count* among diagrams with the same
boundary label, whereas `DiscDiagram.Reduced` is the pairwise no-cancellation
condition; the two agree on what this argument needs, since removing a
cancelling pair drops the count by two.

**Why the named Prop is not a consequence of `Delta.Reduced` alone.**
`Embedded.InteriorEdge` does not require the source cell to differ from the
target cell, and `DiscDiagram.Reduced` only constrains *pairs* of relator cells
occurring in the stored order.  `reduced_of_rCellCount_le_one` shows every
diagram with at most one relator cell is reduced, and
`interiorEdge_source_eq_target_of_rCellCount_one` shows that at exactly one
relator cell every interior edge is self-contiguous.  So at one cell the
reducedness hypothesis is automatic while the inequality is not, and any
producer of the named Prop must either exclude self-contiguous candidates or
derive the inequality from something other than `Delta.Reduced`.  This is
recorded as a model test, not as a refutation: it locates the remaining
content.

**Where the exclusion cannot go.**  Adding a `source_ne_target` conjunct to
`Embedded.InteriorEdge` would cut that type down, but `InteriorEdge` is the
codomain of `Embedded.interiorIncidenceEquiv :
InteriorIncidence selected ≃ InteriorEdge selected × Bool`, and a
self-contiguous candidate still contributes two incidences, so the equivalence
and the counting lemmas `InteriorEdge.edgesCovered_univ` and
`InteriorEdge.hasAtMostTwoEndpoints` that `Assembly.lean` consumes for the
`10 * mu` interior budget would break.  Adding a field to `Embedded.Contiguity`
instead reaches seven construction sites in the hull44 and hull49 lanes, most
of them boundary contiguities where the clause is vacuous.  Both are real
costs, so the exclusion is left as part of the named Prop rather than imposed
on the shared types.

**How the Prop is to be discharged.**
`VanKampen.CellContiguity.whole_relators_ne` concludes exactly this
inequality, for the cells' stored words, from `DiscDiagram.Reduced` plus a
`CellContiguity` certificate, and
`Embedded.ReducedCellPieceBridge.of_cellContiguity` converts such a
certificate into the bridge consumed above.  So the certificate is the data to
carry, and it is precisely the data Osin's `O52` argument uses: the stored-order
`split` at the two cells and the connector identity `leftConnector_transport`.

Carrying it on `Embedded.Contiguity` is possible without new imports.  All six
components are expressible there: the split and the two `reversed = false`
flags from `DiscDiagram`; the source alignment
`listVal (dartWord Delta sourceArc.rotated) = listVal (cell Delta source).word`;
the target alignment
`listVal (dartWord Delta targetArc.rotated) = listVal (cell Delta i).word`,
which needs no cast because `CyclicArc.rotated` returns a plain dart list; and
the connector identity
`listVal (dartWord Delta rightSide) =
  (cell Delta source).conjugator⁻¹ * (between.map RelatorCell.value).prod *
    (cell Delta i).conjugator`.
The burden then moves to whoever builds candidates, that is est's Lemma 65(a)
construction behind `EstimatingSelectionConstructionStatement`, which must
supply those six components when it produces a region.

**The one piece of algebra that remains.**  `Contiguity.targetInverseCarrier`
is a *rotation* of `RelWord.revInv` of the target arc word, and a rotation
changes `listVal` by conjugation, so the target alignment above does not
immediately give the carrier identification `of_cellContiguity` wants.  Closing
that is bookkeeping about the rotation prefix, not new geometry.

**The gap this replaces.**
`Reduced` constrains `RelatorCell.value` products across the stored cell order,
while the inequality is about `GGT.RelLetter.listVal` of *dart* words on the
region's arcs.  `Embedded.Contiguity` bounds `rightSide` only in length and
norm, so nothing currently ties `listVal (dartWord Delta rightSide)` to the
cells' conjugators and the intervening value product.  That is the
`leftConnector_transport` component listed above.
-/

set_option linter.unusedVariables false

namespace GroupApproximation
namespace GGT
namespace VanKampen

universe u w v

namespace Embedded

/-- **The two-arc certificate at one embedded region, from its pasting.**  The
boundary-dart equation is the trivial-value statement for the region's boundary
cycle, which is exactly what a face-set word homotopy to the empty word says.
The non-cancellation clause is the only other input.  This is the form to use:
a producer of pastings never has to be unpacked. -/
def cellPieceEquations_of_pasting
    {G : Type u} [Group G] {Lambda : Type w}
    {D : GGT.RelGenSet G Lambda} {eps : ℕ}
    {W : Set (List (GGT.RelLetter G Lambda))}
    {Delta : DiscDiagram.{u, w, v} W}
    {faces : Finset Delta.toCombMap.Face}
    (Gamma : Contiguity D eps Delta faces)
    (pasting : FaceSetWordHomotopy Delta faces Gamma.boundary.cycle [])
    {target : Fin Delta.rCellCount}
    (htarget : Gamma.target = some target)
    (hne : GGT.RelLetter.listVal (Gamma.targetInverseCarrier target htarget) ≠
      (GGT.RelLetter.listVal (dartWord Delta Gamma.rightSide))⁻¹ *
        GGT.RelLetter.listVal (dartWord Delta Gamma.sourceArc.rotated) *
        GGT.RelLetter.listVal (dartWord Delta Gamma.rightSide)) :
    CellPieceEquations Gamma :=
  CellPieceEquations.of_boundary_equation Gamma htarget
    (Gamma.targetBoundary_value_of_pasting pasting) hne

/-- **The region's own pasting.**  `Contiguity.pasting` carries a shelling of
the boundary cycle, and `faceSetWordHomotopy_of_shelling` turns it into the
homotopy.  So no producer, no ear and no shelling statement is needed: the
region supplies its own. -/
theorem contiguity_pasting
    {G : Type u} [Group G] {Lambda : Type w}
    {D : GGT.RelGenSet G Lambda} {eps : ℕ}
    {W : Set (List (GGT.RelLetter G Lambda))}
    {Delta : DiscDiagram.{u, w, v} W}
    {faces : Finset Delta.toCombMap.Face}
    (Gamma : Contiguity D eps Delta faces) :
    FaceSetWordHomotopy Delta faces Gamma.boundary.cycle [] := by
  obtain ⟨l, shelling⟩ := Gamma.pasting
  exact faceSetWordHomotopy_of_shelling shelling

/-- **The two-arc certificate with no hypothesis at all.**  The boundary-dart
equation comes from the region's own `pasting` field; the non-cancellation
clause comes from its `o52Certificate` field and `Delta.Reduced`. -/
def cellPieceEquations_of_contiguity
    {G : Type u} [Group G] {Lambda : Type w}
    {D : GGT.RelGenSet G Lambda} {eps : ℕ}
    {W : Set (List (GGT.RelLetter G Lambda))}
    {Delta : DiscDiagram.{u, w, v} W}
    {faces : Finset Delta.toCombMap.Face}
    (Gamma : Contiguity D eps Delta faces)
    {target : Fin Delta.rCellCount}
    (htarget : Gamma.target = some target)
    (hne : GGT.RelLetter.listVal (Gamma.targetInverseCarrier target htarget) ≠
      (GGT.RelLetter.listVal (dartWord Delta Gamma.rightSide))⁻¹ *
        GGT.RelLetter.listVal (dartWord Delta Gamma.sourceArc.rotated) *
        GGT.RelLetter.listVal (dartWord Delta Gamma.rightSide)) :
    CellPieceEquations Gamma :=
  cellPieceEquations_of_pasting Gamma (contiguity_pasting Gamma) htarget hne

/-- **The non-cancellation clause of a region, from reducedness alone.**  The
region's `o52Certificate` field plus `Delta.Reduced` give it; no producer and no
`InteriorEdge` packaging is involved. -/
theorem Contiguity.whole_ne_of_reduced
    {G : Type u} [Group G] {Lambda : Type w}
    {D : GGT.RelGenSet G Lambda} {eps : ℕ}
    {W : Set (List (GGT.RelLetter G Lambda))}
    {Delta : DiscDiagram.{u, w, v} W}
    {faces : Finset Delta.toCombMap.Face}
    (Gamma : Contiguity D eps Delta faces)
    (hred : Delta.Reduced)
    {target : Fin Delta.rCellCount} (htarget : Gamma.target = some target) :
    GGT.RelLetter.listVal (Gamma.targetInverseCarrier target htarget) ≠
      (GGT.RelLetter.listVal (dartWord Delta Gamma.rightSide))⁻¹ *
        GGT.RelLetter.listVal (dartWord Delta Gamma.sourceArc.rotated) *
        GGT.RelLetter.listVal (dartWord Delta Gamma.rightSide) := by
  obtain ⟨pre, between, suf, hsplit, hsf, htf, hsource, htargetword, hconn⟩ :=
    Gamma.o52Certificate target htarget
  refine whole_ne_of_certificate Gamma target htarget hred hsplit hsf htf
    hsource ?_ ?_
  · rw [targetArcAtSome_rotated]
    exact htargetword
  · rw [targetArcAtSome_darts]
    exact hconn

/-- **The two-arc certificate of a region, from reducedness alone.**  Both
inputs are fields: `pasting` for the boundary-dart equation and
`o52Certificate` for the non-cancellation clause. -/
def Contiguity.cellPieceEquations_of_reduced
    {G : Type u} [Group G] {Lambda : Type w}
    {D : GGT.RelGenSet G Lambda} {eps : ℕ}
    {W : Set (List (GGT.RelLetter G Lambda))}
    {Delta : DiscDiagram.{u, w, v} W}
    {faces : Finset Delta.toCombMap.Face}
    (Gamma : Contiguity D eps Delta faces)
    (hred : Delta.Reduced)
    {target : Fin Delta.rCellCount} (htarget : Gamma.target = some target) :
    CellPieceEquations Gamma :=
  cellPieceEquations_of_contiguity Gamma htarget
    (Gamma.whole_ne_of_reduced hred htarget)

/-- The same certificate from the ear statement, which produces the pasting via
a face-deletion schedule.  Kept as a corollary; both it and
`RegionShellingStatement` are now superseded by the `pasting` field. -/
def cellPieceEquations_of_earStatement
    (hear : FaceSetEarStatement.{u, w, v})
    {G : Type u} [Group G] {Lambda : Type w}
    {D : GGT.RelGenSet G Lambda} {eps : ℕ}
    {W : Set (List (GGT.RelLetter G Lambda))}
    {Delta : DiscDiagram.{u, w, v} W}
    {faces : Finset Delta.toCombMap.Face}
    (Gamma : Contiguity D eps Delta faces)
    {target : Fin Delta.rCellCount}
    (htarget : Gamma.target = some target)
    (hne : GGT.RelLetter.listVal (Gamma.targetInverseCarrier target htarget) ≠
      (GGT.RelLetter.listVal (dartWord Delta Gamma.rightSide))⁻¹ *
        GGT.RelLetter.listVal (dartWord Delta Gamma.sourceArc.rotated) *
        GGT.RelLetter.listVal (dartWord Delta Gamma.rightSide)) :
    CellPieceEquations Gamma :=
  CellPieceEquations.of_boundary_equation Gamma htarget
    (Gamma.targetBoundary_value_of_pasting
      (faceSetBoundaryPeeling_of_earStatement hear Gamma.boundary).to_homotopy)
    hne

end Embedded

/-! ## The single remaining local input -/

/-- **The one local inequality still missing from the Piece construction.**
For a reduced diagram, no selected interior candidate has its target relator
carrier equal to the source relator rotated and conjugated by the region's
short right side.  This is the `whole_ne` field of `CellPieceEquations` and
nothing more; the other two fields are proved above. -/
def EstimatingPieceNonCancellationStatement : Prop :=
  ∀ {G : Type u} [Group G] {Lambda : Type w}
    (D : GGT.RelGenSet G Lambda) (eps : ℕ)
    {W : Set (List (GGT.RelLetter G Lambda))}
    (Delta : DiscDiagram.{u, w, v} W)
    (selected : Finset (Embedded.Candidate D eps Delta)),
    Delta.Reduced →
    ∀ (edge : Embedded.InteriorEdge selected)
      (target : Fin Delta.rCellCount)
      (htarget : edge.candidate.contiguity.target = some target),
      GGT.RelLetter.listVal
          (edge.candidate.contiguity.targetInverseCarrier target htarget) ≠
        (GGT.RelLetter.listVal (Embedded.dartWord Delta
            edge.candidate.contiguity.rightSide))⁻¹ *
          GGT.RelLetter.listVal (Embedded.dartWord Delta
            edge.candidate.contiguity.sourceArc.rotated) *
          GGT.RelLetter.listVal (Embedded.dartWord Delta
            edge.candidate.contiguity.rightSide)

/-- The landed reduced-bridge route supplies the named Prop.  The bridge stores
the same inequality once the target index is identified, which is the exact
sense in which the named Prop is no larger than the bridge family. -/
theorem estimatingPieceNonCancellation_of_reducedBridges
    (hbridge : ∀ {G : Type u} [Group G] {Lambda : Type w}
      (D : GGT.RelGenSet G Lambda) (eps : ℕ)
      {W : Set (List (GGT.RelLetter G Lambda))}
      (Delta : DiscDiagram.{u, w, v} W)
      (selected : Finset (Embedded.Candidate D eps Delta)),
      Delta.Reduced →
      ∀ edge : Embedded.InteriorEdge selected,
        Nonempty (Embedded.ReducedCellPieceBridge edge.candidate.contiguity)) :
    EstimatingPieceNonCancellationStatement.{u, w, v} := by
  intro G _ Lambda D eps W Delta selected hred edge target htarget
  obtain ⟨bridge⟩ := hbridge D eps Delta selected hred edge
  have hsome : some bridge.target = some target :=
    bridge.target_eq.symm.trans htarget
  have hidx : bridge.target = target := Option.some.inj hsome
  subst hidx
  exact bridge.whole_ne hred

/-- **The named Prop, discharged.**  Every selected interior candidate carries
Osin's `O52` certificate as a field of `Embedded.Contiguity`, and reducedness
turns it into the non-cancellation inequality.  No hypothesis remains. -/
theorem estimatingPieceNonCancellationStatement :
    EstimatingPieceNonCancellationStatement.{u, w, v} := by
  intro G _ Lambda D eps W Delta selected hred edge target htarget
  obtain ⟨pre, between, suf, hsplit, hsf, htf, hsource, htargetword, hconn⟩ :=
    edge.candidate.contiguity.o52Certificate target htarget
  refine Embedded.whole_ne_of_certificate edge.candidate.contiguity target
    htarget hred hsplit hsf htf hsource ?_ ?_
  · rw [Embedded.targetArcAtSome_rotated]
    exact htargetword
  · rw [Embedded.targetArcAtSome_darts]
    exact hconn

/-! ## Model tests -/


/-- A diagram with at most one relator cell is reduced: the no-cancelling-pair
condition quantifies over a split exhibiting two listed cells. -/
theorem reduced_of_rCellCount_le_one
    {G : Type u} [Group G] {Lambda : Type w}
    {W : Set (List (GGT.RelLetter G Lambda))}
    (Delta : DiscDiagram.{u, w, v} W) (h : Delta.rCellCount ≤ 1) :
    Delta.Reduced := by
  intro pre between suf C₁ C₂ hsplit
  have h' : Delta.relatorCells.length ≤ 1 := h
  have hlen := congrArg List.length hsplit
  simp only [List.length_append, List.length_cons] at hlen
  exfalso
  omega

/-- Model test at exactly one relator cell: every interior edge is
self-contiguous.  With `reduced_of_rCellCount_le_one` this locates the
remaining content of the named Prop, since reducedness is automatic there. -/
theorem interiorEdge_source_eq_target_of_rCellCount_one
    {G : Type u} [Group G] {Lambda : Type w}
    {D : GGT.RelGenSet G Lambda} {eps : ℕ}
    {W : Set (List (GGT.RelLetter G Lambda))}
    {Delta : DiscDiagram.{u, w, v} W}
    {selected : Finset (Embedded.Candidate D eps Delta)}
    (hone : Delta.rCellCount = 1)
    (edge : Embedded.InteriorEdge selected) :
    edge.candidate.contiguity.source = edge.target := by
  apply Fin.ext
  have h1 := edge.candidate.contiguity.source.isLt
  have h2 := edge.target.isLt
  omega

/-- Model test at the empty relator family: the body of the named Prop holds,
because an interior edge carries a relator-cell index and there is none. -/
theorem estimatingPieceNonCancellation_holds_of_rCellCount_zero
    {G : Type u} [Group G] {Lambda : Type w}
    (D : GGT.RelGenSet G Lambda) (eps : ℕ)
    {W : Set (List (GGT.RelLetter G Lambda))}
    (Delta : DiscDiagram.{u, w, v} W)
    (selected : Finset (Embedded.Candidate D eps Delta))
    (hzero : Delta.rCellCount = 0)
    (hred : Delta.Reduced)
    (edge : Embedded.InteriorEdge selected)
    (target : Fin Delta.rCellCount)
    (htarget : edge.candidate.contiguity.target = some target) :
    GGT.RelLetter.listVal
        (edge.candidate.contiguity.targetInverseCarrier target htarget) ≠
      (GGT.RelLetter.listVal (Embedded.dartWord Delta
          edge.candidate.contiguity.rightSide))⁻¹ *
        GGT.RelLetter.listVal (Embedded.dartWord Delta
          edge.candidate.contiguity.sourceArc.rotated) *
        GGT.RelLetter.listVal (Embedded.dartWord Delta
          edge.candidate.contiguity.rightSide) :=
  absurd target.isLt (by omega)

/-- Model test at exactly one relator cell: there are no interior edges at all,
because `target_ne_source` and a single cell index are incompatible. -/
theorem no_interiorEdge_of_rCellCount_one
    {G : Type u} [Group G] {Lambda : Type w}
    {D : GGT.RelGenSet G Lambda} {eps : ℕ}
    {W : Set (List (GGT.RelLetter G Lambda))}
    {Delta : DiscDiagram.{u, w, v} W}
    {selected : Finset (Embedded.Candidate D eps Delta)}
    (hone : Delta.rCellCount = 1)
    (edge : Embedded.InteriorEdge selected) : False :=
  edge.candidate.contiguity.target_ne_source edge.target edge.target_eq
    (interiorEdge_source_eq_target_of_rCellCount_one hone edge)

end VanKampen
end GGT
end GroupApproximation
