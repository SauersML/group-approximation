import GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.WitnessStepPinchRegion
import GroupApproximation.Meta.AxiomGuard

/-!
# Greendlinger leaf P07, lane gl-p07-52: the junction facts of `Γ = G₁ · B · G₂ · A`

Lane gl-p07-52.  Certifies no printed sentence on its own.  NOT COMPILED.

Write `B = b.sideFrom i`, `A = a.sideFrom j`, and let `K₁ = a_i · G₁ · b_i`, `K₂ = b_j · G₂ · a_j`
be the two cell arcs of the pocket walk.  `F` is off both regions and off both cells.  Each
junction fact is a σ-fan (`WitnessStepPinchFan`) from `α d`, `d` the last dart of a piece, to the
first dart `g` of the next nonempty piece.  The fan is a composite of region joints
(`WitnessStepPinchRegion.lean`) and face steps along `K₁`, `K₂`.  The middle darts are cell-arc
darts of a region, or their reverses, so both of their faces are off `F`.
* `witnessStepPinch_junction_B_G₂`: `B → G₂` (via `α z`, `z` the last dart of `b_j`).
* `witnessStepPinch_junction_G₂_A`: `G₂ → A` (via `z'`, the first dart of `a_j`).
* `witnessStepPinch_junction_A_G₁`: `A → G₁` (via `α z''`, `z''` the last dart of `a_i`).
* `witnessStepPinch_junction_B_A`: `B → A` when `G₂ = []` (via `α z`, `z'`).
* `witnessStepPinch_junction_G₂_G₁`: `G₂ → G₁` when `A = []` (via `z'`, `α z''`).
* `witnessStepPinch_junction_B_G₁`: `B → G₁` when `G₂ = A = []` (via `α z`, `z'`, `α z''`).
All six are TRUE as formalized, and proved here from the data.
-/

namespace GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket

universe u w v

open Embedded HullSC WordMetric SimpleClosedWalkSides Surgery.MapCollapse

namespace FourPieceWitness

/-- A nonempty list has a last element. -/
theorem witnessStepPinch_exists_last {β : Type*} {L : List β} (h : 0 < L.length) :
    ∃ (q : List β) (z : β), L = q ++ [z] :=
  ⟨L.dropLast, L.getLast (List.ne_nil_of_length_pos h),
    (List.dropLast_append_getLast (List.ne_nil_of_length_pos h)).symm⟩

#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.FourPieceWitness.witnessStepPinch_exists_last

section PinchJunction

variable {G : Type u} [Group G] {Lambda : Type w} {W : Set (List (RelLetter G Lambda))}
  {D : RelGenSet G Lambda} {eps : ℕ} {X : DiscDiagram.{u, w, v} W} {i j : Fin X.rCellCount}

/-- **Junction `B → G₂`.** -/
theorem witnessStepPinch_junction_B_G₂ {a b : RegionCandidate D eps X}
    {G₂ : CyclicArc (cellDarts X j)} {F : Finset X.toCombMap.Face}
    (hFb : ∀ f ∈ F, f ∉ b.1) (hFj : (cell X j).face ∉ F) (hij : i ≠ j) (hbi : b.JoinsCells i j)
    (hbj₁ : 0 < (b.cellArcList j).length) (K₂ : CyclicArc (cellDarts X j))
    (hK₂ : K₂.darts = b.cellArcList j ++ G₂.darts ++ a.cellArcList j)
    {p r : List X.toCombMap.Dart} {d g : X.toCombMap.Dart} (hS : b.sideFrom i = p ++ [d])
    (hG : G₂.darts = g :: r) : WitnessStepPinchFan X.toCombMap F (X.toCombMap.alpha d) g := by
  obtain ⟨q, z, hq⟩ := witnessStepPinch_exists_last hbj₁
  have hzK : z ∈ K₂.darts := by
    rw [hK₂, hq]
    simp
  have hzb : z ∈ b.cellArcList j := by
    rw [hq]
    simp
  have hm := witnessStepPinch_arc_mid_faces_alpha hFb hbi hFj K₂ hzK hzb
  have hK : K₂.darts = q ++ z :: g :: (r ++ a.cellArcList j) := by
    rw [hK₂, hq, hG]
    simp
  exact witnessStepPinch_fan_trans (witnessStepPinch_fan_sideI_end hFb hij hbi hS hq)
    (witnessStepPinch_fan_of_facePerm (witnessStepPinch_facePerm_of_arc K₂ hK)) hm.1 hm.2

#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.FourPieceWitness.witnessStepPinch_junction_B_G₂

/-- **Junction `G₂ → A`.** -/
theorem witnessStepPinch_junction_G₂_A {a b : RegionCandidate D eps X}
    {G₂ : CyclicArc (cellDarts X j)} {F : Finset X.toCombMap.Face}
    (hFa : ∀ f ∈ F, f ∉ a.1) (hFj : (cell X j).face ∉ F) (hij : i ≠ j) (hai : a.JoinsCells i j)
    (haj₁ : 0 < (a.cellArcList j).length) (K₂ : CyclicArc (cellDarts X j))
    (hK₂ : K₂.darts = b.cellArcList j ++ G₂.darts ++ a.cellArcList j)
    {p r : List X.toCombMap.Dart} {d g : X.toCombMap.Dart} (hG : G₂.darts = p ++ [d])
    (hS : a.sideFrom j = g :: r) :
    WitnessStepPinchFan X.toCombMap F (X.toCombMap.alpha d) g := by
  obtain ⟨z', q, hq⟩ := List.exists_cons_of_ne_nil (List.ne_nil_of_length_pos haj₁)
  have hzK : z' ∈ K₂.darts := by
    rw [hK₂, hq]
    simp
  have hza : z' ∈ a.cellArcList j := by
    rw [hq]
    simp
  have hm := witnessStepPinch_arc_mid_faces hFa hai hFj K₂ hzK hza
  have hK : K₂.darts = (b.cellArcList j ++ p) ++ d :: z' :: q := by
    rw [hK₂, hG, hq]
    simp
  exact witnessStepPinch_fan_trans
    (witnessStepPinch_fan_of_facePerm (witnessStepPinch_facePerm_of_arc K₂ hK))
    (witnessStepPinch_fan_sideJ_start hFa hij hai hq hS) hm.1 hm.2

#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.FourPieceWitness.witnessStepPinch_junction_G₂_A

/-- **Junction `A → G₁`.** -/
theorem witnessStepPinch_junction_A_G₁ {a b : RegionCandidate D eps X}
    {G₁ : CyclicArc (cellDarts X i)} {F : Finset X.toCombMap.Face}
    (hFa : ∀ f ∈ F, f ∉ a.1) (hFi : (cell X i).face ∉ F) (hij : i ≠ j) (hai : a.JoinsCells i j)
    (hai₁ : 0 < (a.cellArcList i).length) (K₁ : CyclicArc (cellDarts X i))
    (hK₁ : K₁.darts = a.cellArcList i ++ G₁.darts ++ b.cellArcList i)
    {p r : List X.toCombMap.Dart} {d g : X.toCombMap.Dart} (hS : a.sideFrom j = p ++ [d])
    (hG : G₁.darts = g :: r) : WitnessStepPinchFan X.toCombMap F (X.toCombMap.alpha d) g := by
  obtain ⟨q, z'', hq⟩ := witnessStepPinch_exists_last hai₁
  have hzK : z'' ∈ K₁.darts := by
    rw [hK₁, hq]
    simp
  have hza : z'' ∈ a.cellArcList i := by
    rw [hq]
    simp
  have hm := witnessStepPinch_arc_mid_faces_alpha hFa hai hFi K₁ hzK hza
  have hK : K₁.darts = q ++ z'' :: g :: (r ++ b.cellArcList i) := by
    rw [hK₁, hq, hG]
    simp
  exact witnessStepPinch_fan_trans (witnessStepPinch_fan_sideJ_end hFa hij hai hS hq)
    (witnessStepPinch_fan_of_facePerm (witnessStepPinch_facePerm_of_arc K₁ hK)) hm.1 hm.2

#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.FourPieceWitness.witnessStepPinch_junction_A_G₁
