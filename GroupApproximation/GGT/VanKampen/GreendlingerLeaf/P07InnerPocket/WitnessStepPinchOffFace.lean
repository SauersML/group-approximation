import GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.WitnessStepPinchOffStatement
import GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.WitnessStepSkipVertex
import GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.WitnessStepCornerFace
import GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.PocketClassCells
import GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.PocketRunStep
import GroupApproximation.Meta.AxiomGuard

/-!
# Greendlinger leaf P07, lane gl-p07-53: the lobe face of a pinch is closed

Lane gl-p07-53.  Certifies no printed sentence on its own.  NOT COMPILED.

At a pinch `g` of the curve `Γ = G₁ · b.sideFrom i · G₂ · a.sideFrom j`, the lobe face
`faceOf (α g)` is not open (`witnessStepPinchOff_not_open`), and lies in the cut when `g` is a
dart of `G₁` or `G₂` (`witnessStepPinchOff_mem_cut`).  `witnessStepPinchOff_at_of_pinchAt` turns
a pinch into an off-lobe pinch.  See `WitnessStepPinchOffStatement.lean` for the route, the truth
check and the LOUD notes.
-/

namespace GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket

universe u w v

open Embedded HullSC WordMetric SimpleClosedWalkSides Surgery.MapCollapse

namespace FourPieceWitness

section PinchOffFace

variable {G : Type u} [Group G] {Lambda : Type w} {W : Set (List (RelLetter G Lambda))}
  {D : RelGenSet G Lambda} {eps : ℕ} {X : DiscDiagram.{u, w, v} W} {i j : Fin X.rCellCount}

/-- A dart right after `d` in a list is in the list. -/
theorem witnessStepPinchOff_mem_of_append {L p q : List X.toCombMap.Dart}
    {d g : X.toCombMap.Dart} (h : L = p ++ d :: g :: q) : g ∈ L := by
  rw [h]
  simp

#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.FourPieceWitness.witnessStepPinchOff_mem_of_append

/-- The head of a list is in the list. -/
theorem witnessStepPinchOff_mem_of_cons {L q : List X.toCombMap.Dart} {g : X.toCombMap.Dart}
    (h : L = g :: q) : g ∈ L := by
  rw [h]
  simp

#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.FourPieceWitness.witnessStepPinchOff_mem_of_cons

/-- **The pinch dart is on a piece of the curve.** -/
theorem witnessStepPinchOff_mem_pieces {a b : RegionCandidate D eps X}
    {G₁ : CyclicArc (cellDarts X i)} {G₂ : CyclicArc (cellDarts X j)} {d g : X.toCombMap.Dart}
    (h : WitnessStepSkipPieceNext a b G₁ G₂ d g ∨ WitnessStepPinchJunctionNext a b G₁ G₂ d g) :
    g ∈ G₁.darts ∨ g ∈ b.sideFrom i ∨ g ∈ G₂.darts ∨ g ∈ a.sideFrom j := by
  rcases h with hP | hJ
  · unfold WitnessStepSkipPieceNext at hP
    rcases hP with ⟨p, q, hq⟩ | ⟨p, q, hq⟩ | ⟨p, q, hq⟩ | ⟨p, q, hq⟩
    · exact Or.inl (witnessStepPinchOff_mem_of_append hq)
    · exact Or.inr (Or.inl (witnessStepPinchOff_mem_of_append hq))
    · exact Or.inr (Or.inr (Or.inl (witnessStepPinchOff_mem_of_append hq)))
    · exact Or.inr (Or.inr (Or.inr (witnessStepPinchOff_mem_of_append hq)))
  · unfold WitnessStepPinchJunctionNext at hJ
    rcases hJ with ⟨-, ⟨q, hq⟩ | ⟨-, ⟨q, hq⟩ | ⟨-, q, hq⟩⟩⟩ | ⟨-, ⟨q, hq⟩ | ⟨-, q, hq⟩⟩ |
        ⟨-, q, hq⟩
    all_goals
      first
        | exact Or.inl (witnessStepPinchOff_mem_of_cons hq)
        | exact Or.inr (Or.inl (witnessStepPinchOff_mem_of_cons hq))
        | exact Or.inr (Or.inr (Or.inl (witnessStepPinchOff_mem_of_cons hq)))
        | exact Or.inr (Or.inr (Or.inr (witnessStepPinchOff_mem_of_cons hq)))

#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.FourPieceWitness.witnessStepPinchOff_mem_pieces

/-- **A dart of the curve has its face off `F`.**  The faces of `Π_i`, `Π_j`, `a` and `b` are off
`F`. -/
theorem witnessStepPinchOff_faceOf_not_mem {a b : RegionCandidate D eps X}
    {G₁ : CyclicArc (cellDarts X i)} {G₂ : CyclicArc (cellDarts X j)}
    {F : Finset X.toCombMap.Face} (hFa : ∀ f ∈ F, f ∉ a.1) (hFb : ∀ f ∈ F, f ∉ b.1)
    (hFi : (cell X i).face ∉ F) (hFj : (cell X j).face ∉ F) {g : X.toCombMap.Dart}
    (hg : g ∈ G₁.darts ∨ g ∈ b.sideFrom i ∨ g ∈ G₂.darts ∨ g ∈ a.sideFrom j) :
    X.toCombMap.faceOf g ∉ F := by
  rcases hg with hg | hg | hg | hg
  · rw [Embedded.faceOf_of_mem_cellDarts (G₁.mem_cycle_of_mem_darts hg)]
    exact hFi
  · exact fun hf => hFb _ hf (witnessStepCorner_faceOf_mem_of_mem_sideFrom b i hg)
  · rw [Embedded.faceOf_of_mem_cellDarts (G₂.mem_cycle_of_mem_darts hg)]
    exact hFj
  · exact fun hf => hFa _ hf (witnessStepCorner_faceOf_mem_of_mem_sideFrom a j hg)

#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.FourPieceWitness.witnessStepPinchOff_faceOf_not_mem

/-- **Across an unwalked dart off `F`, the face is off `F`.**  From `mem_iff` of the enclosing
walk. -/
theorem witnessStepPinchOff_alpha_faceOf_not_mem {F : Finset X.toCombMap.Face}
    {ow : List X.toCombMap.Dart} (E : EnclosedFaceSetSucc X F ow) {g : X.toCombMap.Dart}
    (hg : g ∉ ow) (hgF : X.toCombMap.faceOf g ∉ F) :
    X.toCombMap.faceOf (X.toCombMap.alpha g) ∉ F :=
  fun hf => hg ((E.mem_iff g).mpr ⟨hgF, Or.inl hf⟩)

#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.FourPieceWitness.witnessStepPinchOff_alpha_faceOf_not_mem

/-- **The lobe face touches the face of `y`.**  `faceOf (α g) = faceOf (σ g)`, and `σ g` sits at
the vertex of `g`, which is the vertex of `y`. -/
theorem witnessStepPinchOff_touch {g y : X.toCombMap.Dart}
    (hv : X.toCombMap.vertexOf g = X.toCombMap.vertexOf y) :
    Touch X.toCombMap (X.toCombMap.faceOf y) (X.toCombMap.faceOf (X.toCombMap.alpha g)) := by
  have h1 : X.toCombMap.facePerm (X.toCombMap.alpha g) = X.toCombMap.sigma g := by
    rw [PocketRun.facePerm_eq_sigma_alpha, X.toCombMap.alpha_involutive g]
  have hface : X.toCombMap.faceOf (X.toCombMap.sigma g) =
      X.toCombMap.faceOf (X.toCombMap.alpha g) := by
    rw [← h1]
    exact X.toCombMap.faceOf_facePerm _
  refine Or.inr ⟨y, X.toCombMap.sigma g, rfl, hface, ?_⟩
  rw [X.toCombMap.vertexOf_sigma, hv]

#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.FourPieceWitness.witnessStepPinchOff_touch
