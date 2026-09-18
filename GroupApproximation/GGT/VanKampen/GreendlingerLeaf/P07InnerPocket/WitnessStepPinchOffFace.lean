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

/-- **The lobe face of a pinch is not open.**  It touches the witness face `faceOf y` at the
vertex of `y`, so if it were open, one more step would put it in `F`. -/
theorem witnessStepPinchOff_not_open {a b : RegionCandidate D eps X}
    {K : CellPocketWalk D eps X i j} {c : X.toCombMap.Face} {ow : List X.toCombMap.Dart}
    (E : EnclosedFaceSetSucc X (witnessFaces a b K c) ow)
    (hnb : ∀ d ∈ ow, X.toCombMap.faceOf (X.toCombMap.alpha d) ∈ witnessFaces a b K c)
    {n : ℕ} {s t : List X.toCombMap.Dart} {x y g : X.toCombMap.Dart}
    (hr : (invDarts X ow).rotate n = s ++ x :: y :: t)
    (hv : X.toCombMap.vertexOf g = X.toCombMap.vertexOf (X.toCombMap.alpha x))
    (hαF : X.toCombMap.faceOf (X.toCombMap.alpha g) ∉ witnessFaces a b K c) :
    ¬ IsOpenFace a b K c (X.toCombMap.faceOf (X.toCombMap.alpha g)) := by
  intro hopen
  have hy' : y ∈ (invDarts X ow).rotate n := by
    rw [hr]
    simp
  have hyF : X.toCombMap.faceOf y ∈ witnessFaces a b K c := by
    have h := hnb _ (witnessStepCorner_alpha_mem_of_mem_invDarts (List.mem_rotate.mp hy'))
    rwa [X.toCombMap.alpha_involutive y] at h
  obtain ⟨hyo, hyr⟩ := mem_witnessFaces_iff.mp hyF
  have hvy : X.toCombMap.vertexOf g = X.toCombMap.vertexOf y :=
    hv.trans (witnessStepSkip_vertexOf_of_rotate E hr)
  have hstep : Step a b K c (X.toCombMap.faceOf y) (X.toCombMap.faceOf (X.toCombMap.alpha g)) :=
    ⟨hyo, hopen, witnessStepPinchOff_touch hvy⟩
  exact hαF (mem_witnessFaces_iff.mpr ⟨hopen, Relation.ReflTransGen.tail hyr hstep⟩)

#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.FourPieceWitness.witnessStepPinchOff_not_open

/-- **On a cell arc, the lobe face of a pinch is in the cut.**  `α g` is a dart of `K.walk`, so
the lobe face is a side face of `K.walk`, and it is not open. -/
theorem witnessStepPinchOff_mem_cut {a b : RegionCandidate D eps X}
    {K : CellPocketWalk D eps X i j} {c : X.toCombMap.Face}
    {G₁ : CyclicArc (cellDarts X i)} {G₂ : CyclicArc (cellDarts X j)}
    (hG₁ : K.firstArc.darts = a.cellArcList i ++ G₁.darts ++ b.cellArcList i)
    (hG₂ : K.secondArc.darts = b.cellArcList j ++ G₂.darts ++ a.cellArcList j)
    {g : X.toCombMap.Dart} (hcell : g ∈ G₁.darts ∨ g ∈ G₂.darts)
    (hopen : ¬ IsOpenFace a b K c (X.toCombMap.faceOf (X.toCombMap.alpha g))) :
    X.toCombMap.faceOf (X.toCombMap.alpha g) ∈ cut a b K c := by
  have hwalk : X.toCombMap.alpha g ∈ K.walk := by
    rcases hcell with hg | hg
    · apply PocketClass.mem_walk_of_mem_invDarts_firstArc K
      apply witnessStepCorner_mem_invDarts_of_alpha_mem
      rw [X.toCombMap.alpha_involutive g, hG₁]
      exact List.mem_append_left _ (List.mem_append_right _ hg)
    · apply PocketClass.mem_walk_of_mem_invDarts_secondArc K
      apply witnessStepCorner_mem_invDarts_of_alpha_mem
      rw [X.toCombMap.alpha_involutive g, hG₂]
      exact List.mem_append_left _ (List.mem_append_right _ hg)
  have hside : X.toCombMap.faceOf (X.toCombMap.alpha g) ∈ sideFaces X.toCombMap K.walk :=
    (mem_sideFaces_iff X.toCombMap K.walk (X.toCombMap.alpha g)).mpr
      ⟨X.toCombMap.alpha g, hwalk, Relation.EqvGen.refl _⟩
  by_contra hc
  exact hopen ⟨hside, hc⟩

#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.FourPieceWitness.witnessStepPinchOff_mem_cut

/-- **Every pinch is an off-lobe pinch**, given the face facts of the premises. -/
theorem witnessStepPinchOff_at_of_pinchAt {a b : RegionCandidate D eps X}
    {K : CellPocketWalk D eps X i j} {c : X.toCombMap.Face}
    {G₁ : CyclicArc (cellDarts X i)} {G₂ : CyclicArc (cellDarts X j)}
    {ow : List X.toCombMap.Dart} (E : EnclosedFaceSetSucc X (witnessFaces a b K c) ow)
    (hnb : ∀ d ∈ ow, X.toCombMap.faceOf (X.toCombMap.alpha d) ∈ witnessFaces a b K c)
    (hFa : ∀ f ∈ witnessFaces a b K c, f ∉ a.1) (hFb : ∀ f ∈ witnessFaces a b K c, f ∉ b.1)
    (hFi : (cell X i).face ∉ witnessFaces a b K c) (hFj : (cell X j).face ∉ witnessFaces a b K c)
    (hG₁ : K.firstArc.darts = a.cellArcList i ++ G₁.darts ++ b.cellArcList i)
    (hG₂ : K.secondArc.darts = b.cellArcList j ++ G₂.darts ++ a.cellArcList j)
    {n : ℕ} {s t : List X.toCombMap.Dart} {x y : X.toCombMap.Dart}
    (hr : (invDarts X ow).rotate n = s ++ x :: y :: t)
    (hp : WitnessStepPinchAt a b G₁ G₂ ow x y) :
    WitnessStepPinchOffAt a b K c G₁ G₂ ow x y := by
  obtain ⟨g, hnext, hg, hv⟩ := hp
  have hgF := witnessStepPinchOff_faceOf_not_mem hFa hFb hFi hFj
    (witnessStepPinchOff_mem_pieces hnext)
  have hαF := witnessStepPinchOff_alpha_faceOf_not_mem E hg hgF
  have hopen := witnessStepPinchOff_not_open E hnb hr hv hαF
  exact ⟨g, hnext, hg, hv, hopen, fun hcell => witnessStepPinchOff_mem_cut hG₁ hG₂ hcell hopen⟩

#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.FourPieceWitness.witnessStepPinchOff_at_of_pinchAt

end PinchOffFace

end FourPieceWitness

end GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket
