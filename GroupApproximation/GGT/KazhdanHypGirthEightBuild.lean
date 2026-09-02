import GroupApproximation.GGT.KazhdanHypGirthEightSlim
import GroupApproximation.GGT.KazhdanHypGirthEightVKInterface
import GroupApproximation.GGT.KazhdanHypGirthEightPrimitives2
import GroupApproximation.GGT.VanKampen.CactusRealization
import GroupApproximation.GGT.VanKampen.CombMapReduction
import GroupApproximation.GGT.VanKampen.CombMapStars

/-!
# The conditional build argument for girth-eight hyperbolicity

This module assembles the exact `build` input of
`GirthEightSlim.presented_isHyperbolicGroup_of_girthEight_layer_construction`.
The algebraic word input is converted to a planar diagram by
`VanKampen.cactusRealizationStatement`.  A relative base-cell elimination
then supplies a reduced relator-only diagram with the same literal boundary.
The remaining local-data and star construction is named as a smaller
conditional input.  Its output is converted to `SuccessiveStarLayers`, and
the four inequalities are passed to the existing metric consumer.

The source operations used here are the face-star disjointness theorem
`CombMap.faceStarLayer_disjoint`, the identity reduction theorem
`VanKampen.identityRelatorOnlyReduction`, and the cactus construction in
`VanKampen.CactusRealization`.  The two geometric existence inputs are not
available in the current map interface, so they are stated separately and
model-tested on the trivial presentation.
-/

namespace GroupApproximation
namespace GGT
namespace KazhdanHypGirthEightBuild

open GroupApproximation.KazhdanHyp
open GroupApproximation.GGT.GirthEightVKInterface
open GroupApproximation.GGT.GirthEightPrimitives2
open GroupApproximation.Manuscript.NonMF.TorsionFree
open GroupApproximation.WordMetric
open scoped BigOperators

section Table

variable {Generator TriangleIndex : Type}
  [Fintype Generator] [DecidableEq Generator]
  [Fintype TriangleIndex] [DecidableEq TriangleIndex]
  {T : TriangleIndex → TriangularHodgeLayer.Triangle Generator}

/-! ## Literal words and the cactus boundary input -/

/-- The free-group letter corresponding to a signed generator. -/
def freeLetter (u : TriangularHodgeLayer.SignedGenerator Generator) :
    FreeGroup Generator :=
  FoxBoundary.letterValue FreeGroup.of u

/-- The relative word obtained from a signed-generator word. -/
def relativeWord (w : List (TriangularHodgeLayer.SignedGenerator Generator)) :
    List (GGT.RelLetter (FreeGroup Generator) PEmpty) :=
  w.map signedFreeRelLetter

/-- The presented-group triviality condition for a literal word. -/
def PresentedWordIsTrivial
    (w : List (TriangularHodgeLayer.SignedGenerator Generator)) : Prop :=
  PresentedGroup.mk
      (TriangularHodgeLayer.relators T : Set (FreeGroup Generator))
      (PresentedGroupRelatorReplay.word w) = 1

/-- An algebraic least-area certificate whose exterior word is the chosen
literal word. -/
structure TrivialWordCactusWitness
    (w : List (TriangularHodgeLayer.SignedGenerator Generator)) where
  /-- The literal word is trivial in the triangularly presented group. -/
  trivial : PresentedWordIsTrivial (T := T) w
  /-- The free base alphabet used by the algebraic diagram. -/
  alphabet : Alphabet (FreeGroup Generator)
  /-- The radius parameter of the algebraic certificate. -/
  radius : ℕ
  /-- The oriented least-area algebraic diagram. -/
  algebraic : HullSC.Lemma44OrientedRelatorDiagram alphabet
    (triangleRelatorWords T) radius
  /-- Its exterior word is the free-group spelling of the literal word. -/
  boundaryWord_eq : algebraic.boundaryWord = w.map freeLetter

/-- The far-point word extraction needed before cactus realization.  It
supplies a nontrivial free-group word which is trivial in the presented group.
The nontrivial free-group clause excludes the empty algebraic boundary, as
required by the least-area cactus interface. -/
def FarPointBoundaryWord : Prop :=
  ∀ (delta : ℕ) (x y z p : TriangularHodgeLayer.Presented T),
    Hyperbolic.IsBetween
      (↑(GirthEightSlim.presentedGeneratorFinset T) :
        Set (TriangularHodgeLayer.Presented T)) x p y →
    (∀ q : TriangularHodgeLayer.Presented T,
      Hyperbolic.IsBetween
        (↑(GirthEightSlim.presentedGeneratorFinset T) :
          Set (TriangularHodgeLayer.Presented T)) x q z →
      delta < wordDist
        (↑(GirthEightSlim.presentedGeneratorFinset T) :
          Set (TriangularHodgeLayer.Presented T)) p q) →
    (∀ q : TriangularHodgeLayer.Presented T,
      Hyperbolic.IsBetween
        (↑(GirthEightSlim.presentedGeneratorFinset T) :
          Set (TriangularHodgeLayer.Presented T)) z q y →
      delta < wordDist
        (↑(GirthEightSlim.presentedGeneratorFinset T) :
          Set (TriangularHodgeLayer.Presented T)) p q) →
    ∃ w : List (TriangularHodgeLayer.SignedGenerator Generator),
      PresentedWordIsTrivial (T := T) w ∧
        (w.map freeLetter).prod ≠ 1

/-- The cactus input for every nontrivial free-group word supplied by
`FarPointBoundaryWord`. -/
def CactusBoundaryInput : Prop :=
  ∀ (w : List (TriangularHodgeLayer.SignedGenerator Generator)),
    PresentedWordIsTrivial (T := T) w →
    (w.map freeLetter).prod ≠ 1 →
    Nonempty (TrivialWordCactusWitness (T := T) w)

/-- The cactus and base-cell bridge has the exact literal boundary required by
the disc-diagram consumer. -/
theorem reducedRelatorOnly_of_cactusBoundary
    (hcactus : CactusBoundaryInput (T := T))
    (hbase : ∀ Delta : VanKampen.DiscDiagram (triangleRelatorWords T),
      Delta.Reduced → Nonempty (RelatorOnlyReduction T Delta))
    (w : List (TriangularHodgeLayer.SignedGenerator Generator))
    (hw : PresentedWordIsTrivial (T := T) w)
    (hfree : (w.map freeLetter).prod ≠ 1) :
    ∃ Delta : VanKampen.DiscDiagram (triangleRelatorWords T),
      Delta.boundaryWord = relativeWord w ∧
      Delta.Reduced ∧ RelatorOnly T Delta := by
  obtain ⟨I⟩ := hcactus w hw hfree
  obtain ⟨C⟩ := VanKampen.cactusRealizationStatement I.algebraic
  obtain ⟨R⟩ := hbase C.diagram C.reduced
  refine ⟨R.diagram, ?_, R.reduced, R.relatorOnly⟩
  calc
    R.diagram.boundaryWord = C.diagram.boundaryWord := R.boundaryWord_eq
    _ = I.algebraic.boundaryWord.map
        (GGT.RelLetter.base : FreeGroup Generator →
          GGT.RelLetter (FreeGroup Generator) PEmpty) := C.boundaryWord_eq
    _ = (w.map freeLetter).map
        (GGT.RelLetter.base : FreeGroup Generator →
          GGT.RelLetter (FreeGroup Generator) PEmpty) :=
      congrArg (List.map (GGT.RelLetter.base : FreeGroup Generator →
        GGT.RelLetter (FreeGroup Generator) PEmpty)) I.boundaryWord_eq
    _ = relativeWord w := by
      rfl

/-! ## Relative base-cell elimination -/

/-- The output shape of the missing relative base-cell elimination theorem. -/
def BaseCellEliminationAt
    (Delta : VanKampen.DiscDiagram (triangleRelatorWords T)) : Prop :=
  Delta.Reduced → Nonempty (RelatorOnlyReduction T Delta)

/-- A global base-cell elimination input for the triangular presentation. -/
def BaseCellElimination : Prop :=
  ∀ Delta : VanKampen.DiscDiagram (triangleRelatorWords T),
    BaseCellEliminationAt (T := T) Delta

omit [Fintype Generator] [DecidableEq Generator]
    [Fintype TriangleIndex] [DecidableEq TriangleIndex] in
/-- A diagram with only its exterior face is eliminated by the named identity
reduction `VanKampen.identityRelatorOnlyReduction`. -/
theorem baseCellEliminationAt_of_noInnerFaces
    (Delta : VanKampen.DiscDiagram (triangleRelatorWords T))
    (hface : ∀ f : Delta.toCombMap.Face, f = Delta.outerFace) :
    BaseCellEliminationAt (T := T) Delta := by
  intro hred
  let cover : VanKampen.RelatorCellCover Delta := {
    cell := fun f hf => (hf (hface f)).elim }
  let I := VanKampen.identityRelatorOnlyReduction Delta cover hred
  refine ⟨{
    diagram := I.diagram
    boundaryWord_eq := I.boundaryWord_eq
    rCellCount_le := ?_
    reduced := I.reduced
    relatorOnly := { cell := I.cover.cell }
  }⟩
  rw [I.rCellCount_eq]

/-- The no-inner-face model is also the empty-boundary model for the
base-cell interface. -/
theorem baseCellEliminationAt_emptyBoundary_model
    (Delta : VanKampen.DiscDiagram (triangleRelatorWords T))
    (hface : ∀ f : Delta.toCombMap.Face, f = Delta.outerFace) :
    BaseCellEliminationAt (T := T) Delta :=
  baseCellEliminationAt_of_noInnerFaces Delta hface

/-! ## Face-star counting used by the final build -/

omit [Fintype Generator] [DecidableEq Generator]
    [Fintype TriangleIndex] [DecidableEq TriangleIndex] in
/-- Intersecting every face-star layer with the inner faces preserves the
pairwise-disjoint cardinality bound.  The disjointness step explicitly uses
`CombMap.faceStarLayer_disjoint`. -/
theorem innerStarLayers_sum_bound_from_combMapStars
    (Delta : VanKampen.DiscDiagram (triangleRelatorWords T))
    (P : BoundarySubpath T Delta) (depth : ℕ) :
    (∑ i : Fin depth,
      (innerBoundaryFaceStarLayer Delta P i).card) ≤ Delta.innerFaceCount := by
  classical
  let seed := boundaryFaceSeed Delta P
  have hpairwise : ((Finset.univ : Finset (Fin depth)) : Set (Fin depth)).PairwiseDisjoint
      (fun i ↦ Delta.toCombMap.faceStarLayer seed i ∩ Delta.innerFaces) := by
    intro i _hi j _hj hij
    exact (Delta.toCombMap.faceStarLayer_disjoint seed (by
      intro hval
      apply hij
      exact Fin.ext hval)).mono Finset.inter_subset_left Finset.inter_subset_left
  change (∑ i : Fin depth,
    (Delta.toCombMap.faceStarLayer (boundaryFaceSeed Delta P) i ∩
      Delta.innerFaces).card) ≤ Delta.innerFaces.card
  rw [← Finset.card_biUnion hpairwise]
  apply Finset.card_le_card
  intro f hf
  obtain ⟨i, _hi, hfi⟩ := Finset.mem_biUnion.mp hf
  exact (Finset.mem_inter.mp hfi).2

/-! ## The local-data and successive-star residual -/

/-- One output of the missing local-data and star construction. -/
structure StarLayerInput
    (Delta : VanKampen.DiscDiagram (triangleRelatorWords T))
    (_L : TriangularDiagramLocalData T Delta) where
  /-- Cayley labels on the diagram vertices. -/
  cayley : CayleyVertexLabelling T Delta
  /-- The centered boundary subpath. -/
  side : BoundarySubpath T Delta
  /-- Number of layers. -/
  depth : ℕ
  /-- Length scale of the centered window. -/
  scale : ℕ
  /-- Endpoint loss. -/
  loss : ℕ
  /-- Maximum face perimeter. -/
  perimeter : ℕ
  /-- The truncated boundary has at most six scale pieces. -/
  boundary_bound : Delta.combinatorialBoundaryLength ≤ 6 * scale
  /-- Every layer covers the surviving part of the centered window. -/
  layer_covers : LayerCoversWindow Delta side depth scale loss perimeter
  /-- The chosen depth exceeds the arithmetic curvature bound. -/
  depth_too_large : 18 * perimeter * scale < depth * (scale - loss)

/-- The remaining local topological input: a reduced cactus output has local
diagram data and a centered star construction with all four numerical fields.
The strict depth inequality is included so the output is immediately usable
by `girthEight_layer_depth_bound`. -/
def StarLayerConstruction : Prop :=
  ∀ (delta : ℕ) (x y z p : TriangularHodgeLayer.Presented T),
    Hyperbolic.IsBetween
      (↑(GirthEightSlim.presentedGeneratorFinset T) :
        Set (TriangularHodgeLayer.Presented T)) x p y →
    (∀ q : TriangularHodgeLayer.Presented T,
      Hyperbolic.IsBetween
        (↑(GirthEightSlim.presentedGeneratorFinset T) :
          Set (TriangularHodgeLayer.Presented T)) x q z →
      delta < wordDist
        (↑(GirthEightSlim.presentedGeneratorFinset T) :
          Set (TriangularHodgeLayer.Presented T)) p q) →
    (∀ q : TriangularHodgeLayer.Presented T,
      Hyperbolic.IsBetween
        (↑(GirthEightSlim.presentedGeneratorFinset T) :
          Set (TriangularHodgeLayer.Presented T)) z q y →
      delta < wordDist
        (↑(GirthEightSlim.presentedGeneratorFinset T) :
          Set (TriangularHodgeLayer.Presented T)) p q) →
    ∀ (Delta : VanKampen.DiscDiagram (triangleRelatorWords T)),
      Delta.Reduced →
      ∃ L : TriangularDiagramLocalData T Delta,
        Nonempty (StarLayerInput (T := T) Delta L)

namespace StarLayerInput

variable {Delta : VanKampen.DiscDiagram (triangleRelatorWords T)}
  {L : TriangularDiagramLocalData T Delta}

/-- The star input is packaged as the interface record consumed by the metric
slim-triangle theorem. -/
noncomputable def toSuccessiveStarLayers (H : StarLayerInput (T := T) Delta L) :
    SuccessiveStarLayers T :=
  successiveStarLayers_of_geometricData Delta L H.cayley H.side H.depth
    H.scale H.loss H.perimeter H.boundary_bound H.layer_covers
    H.depth_too_large

end StarLayerInput

/-! ## The exact build theorem -/

/-- The cactus, base-cell, local-data, and star inputs produce a diagram with
the requested literal boundary and all four inequalities. -/
theorem build_with_boundary
    (hword : FarPointBoundaryWord (T := T))
    (hcactus : CactusBoundaryInput (T := T))
    (hbase : BaseCellElimination (T := T))
    (hstar : StarLayerConstruction (T := T)) :
    ∀ (delta : ℕ) (x y z p : TriangularHodgeLayer.Presented T),
      Hyperbolic.IsBetween
        (↑(GirthEightSlim.presentedGeneratorFinset T) :
          Set (TriangularHodgeLayer.Presented T)) x p y →
      (∀ q : TriangularHodgeLayer.Presented T,
        Hyperbolic.IsBetween
          (↑(GirthEightSlim.presentedGeneratorFinset T) :
            Set (TriangularHodgeLayer.Presented T)) x q z →
        delta < wordDist
          (↑(GirthEightSlim.presentedGeneratorFinset T) :
            Set (TriangularHodgeLayer.Presented T)) p q) →
      (∀ q : TriangularHodgeLayer.Presented T,
        Hyperbolic.IsBetween
          (↑(GirthEightSlim.presentedGeneratorFinset T) :
            Set (TriangularHodgeLayer.Presented T)) z q y →
        delta < wordDist
          (↑(GirthEightSlim.presentedGeneratorFinset T) :
            Set (TriangularHodgeLayer.Presented T)) p q) →
      ∃ (w : List (TriangularHodgeLayer.SignedGenerator Generator))
        (Delta : VanKampen.DiscDiagram (triangleRelatorWords T))
        (L : TriangularDiagramLocalData T Delta)
        (m ell loss rho : ℕ) (layer : Fin m → ℕ),
        PresentedWordIsTrivial (T := T) w ∧
        Delta.boundaryWord = relativeWord w ∧
        Delta.combinatorialBoundaryLength ≤ 6 * ell ∧
        (∑ i, layer i) ≤ Delta.innerFaceCount ∧
        (∀ i, ell - loss ≤ rho * layer i) ∧
        18 * rho * ell < m * (ell - loss) := by
  intro delta x y z p hp hfarXZ hfarZY
  obtain ⟨w, hw, hfree⟩ := hword delta x y z p hp hfarXZ hfarZY
  obtain ⟨Delta, hboundary, hred, _hrelatorOnly⟩ :=
    reducedRelatorOnly_of_cactusBoundary hcactus
      (fun Delta hred => hbase Delta hred) w hw hfree
  obtain ⟨L, ⟨H⟩⟩ := hstar delta x y z p hp hfarXZ hfarZY Delta hred
  let S := H.toSuccessiveStarLayers
  have hsum : (∑ i : Fin S.depth, S.layer i) ≤ S.diagram.innerFaceCount := by
    change (∑ i : Fin H.depth,
      (innerBoundaryFaceStarLayer Delta H.side i).card) ≤ Delta.innerFaceCount
    exact innerStarLayers_sum_bound_from_combMapStars Delta H.side H.depth
  refine ⟨w, S.diagram, S.localData, S.depth, S.scale, S.loss, S.perimeter,
    S.layer, hw, ?_, S.boundary_bound, hsum, S.layer_covers,
    S.depth_too_large⟩
  exact hboundary

/-- The preceding theorem is exactly the `build` argument required by the
existing slim-triangle consumer. -/
theorem build_argument
    (hword : FarPointBoundaryWord (T := T))
    (hcactus : CactusBoundaryInput (T := T))
    (hbase : BaseCellElimination (T := T))
    (hstar : StarLayerConstruction (T := T)) :
    ∀ (delta : ℕ) (x y z p : TriangularHodgeLayer.Presented T),
      Hyperbolic.IsBetween
        (↑(GirthEightSlim.presentedGeneratorFinset T) :
          Set (TriangularHodgeLayer.Presented T)) x p y →
      (∀ q : TriangularHodgeLayer.Presented T,
        Hyperbolic.IsBetween
          (↑(GirthEightSlim.presentedGeneratorFinset T) :
            Set (TriangularHodgeLayer.Presented T)) x q z →
        delta < wordDist
          (↑(GirthEightSlim.presentedGeneratorFinset T) :
            Set (TriangularHodgeLayer.Presented T)) p q) →
      (∀ q : TriangularHodgeLayer.Presented T,
        Hyperbolic.IsBetween
          (↑(GirthEightSlim.presentedGeneratorFinset T) :
            Set (TriangularHodgeLayer.Presented T)) z q y →
        delta < wordDist
          (↑(GirthEightSlim.presentedGeneratorFinset T) :
            Set (TriangularHodgeLayer.Presented T)) p q) →
      ∃ (Delta : VanKampen.DiscDiagram (triangleRelatorWords T))
        (_L : TriangularDiagramLocalData T Delta)
        (m ell loss rho : ℕ) (layer : Fin m → ℕ),
        Delta.combinatorialBoundaryLength ≤ 6 * ell ∧
        (∑ i, layer i) ≤ Delta.innerFaceCount ∧
        (∀ i, ell - loss ≤ rho * layer i) ∧
        18 * rho * ell < m * (ell - loss) := by
  intro delta x y z p hp hfarXZ hfarZY
  obtain ⟨w, Delta, L, m, ell, loss, rho, layer, _hw, _hboundary,
    hperimeter, hsum, hlayer, hdepth⟩ :=
    build_with_boundary hword hcactus hbase hstar delta x y z p hp hfarXZ hfarZY
  exact ⟨Delta, L, m, ell, loss, rho, layer,
    hperimeter, hsum, hlayer, hdepth⟩

/-- The exact slim-triangle conclusion from the conditional build argument. -/
theorem presented_isHyperbolicGroup_of_cactus_star_build
    {d delta : ℕ} (hchecks : KazhdanHyp.GirthEightChecks T d)
    (hword : FarPointBoundaryWord (T := T))
    (hcactus : CactusBoundaryInput (T := T))
    (hbase : BaseCellElimination (T := T))
    (hstar : StarLayerConstruction (T := T)) :
    Hyperbolic.IsHyperbolicGroup (TriangularHodgeLayer.Presented T) :=
  GirthEightSlim.presented_isHyperbolicGroup_of_girthEight_layer_construction
    hchecks (build_argument hword hcactus hbase hstar)

/-! ## Model tests for the named residuals -/

def emptyTriangleTableBuild : PEmpty → TriangularHodgeLayer.Triangle PEmpty :=
  PEmpty.elim

theorem presentedWordIsTrivial_emptyWord_model
    (T : TriangleIndex → TriangularHodgeLayer.Triangle Generator) :
    PresentedWordIsTrivial (T := T) [] := by
  simp [PresentedWordIsTrivial, PresentedGroupRelatorReplay.word]

theorem cactusBoundaryInput_trivialGroup_model :
    CactusBoundaryInput (T := emptyTriangleTableBuild) := by
  intro w _ hfree
  have hfreeOne : (w.map freeLetter).prod = (1 : FreeGroup PEmpty) :=
    Subsingleton.elim _ _
  exact (hfree hfreeOne).elim

theorem farPointBoundaryWord_trivialGroup_model :
    FarPointBoundaryWord (T := emptyTriangleTableBuild) := by
  intro delta x y z p hp hfarXZ hfarZY
  have hfar := hfarXZ x (Hyperbolic.isBetween_left _ x z)
  have hdist : wordDist
      (↑(GirthEightSlim.presentedGeneratorFinset emptyTriangleTableBuild) :
        Set (TriangularHodgeLayer.Presented emptyTriangleTableBuild)) p x = 0 := by
    have hpx : p = x := Subsingleton.elim _ _
    subst p
    exact wordDist_self _ _
  omega

theorem starLayerConstruction_trivialGroup_model :
    StarLayerConstruction (T := emptyTriangleTableBuild) := by
  intro delta x y z p hp hfarXZ hfarZY
  have hfar := hfarXZ x (Hyperbolic.isBetween_left _ x z)
  have hdist : wordDist
      (↑(GirthEightSlim.presentedGeneratorFinset emptyTriangleTableBuild) :
        Set (TriangularHodgeLayer.Presented emptyTriangleTableBuild)) p x = 0 := by
    have hpx : p = x := Subsingleton.elim _ _
    subst p
    exact wordDist_self _ _
  omega

end Table
end KazhdanHypGirthEightBuild
end GGT
end GroupApproximation
