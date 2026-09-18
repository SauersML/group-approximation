import GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.WitnessStepCurveBounce
import GroupApproximation.Meta.AxiomGuard

/-!
# Greendlinger leaf P07, lane gl-p07-66: the doubled pocket curve is a bounce chain

Lane gl-p07-66.  Certifies no printed sentence on its own.  NOT COMPILED: authored without
running Lean.

Let `Γ = b.sideFrom i ++ G₂ ++ a.sideFrom j ++ G₁`.  Write the arcs of `a`, `b` on `Π_i`, `Π_j`
as `b_i = zBi :: Bi`, `b_j = Bj ++ [zBj]`, `a_j = zAj :: Aj`, `a_i = Ai ++ [zAi]` (all nonempty).
Write `Hop' p q` for `Hop (α p) q`.
* `Γ` has U1 for `b` and for `a`: its darts are sides of that region, or based in the face of a
  cell off it, or sides of the other (disjoint) region.
* The four `Hop'` chains:
  - `α zBi :: (b.sideFrom i ++ [α zBj])` is an infix of the rotation
    `Ā_bi · S_bi · Ā_bj · S_bj` of the boundary of `b` (the last entry of `Ā_bi` is `α zBi`, the
    first of `Ā_bj` is `α zBj`), so a `Hop'` chain under U1 for `b`;
  - `zBj :: (G₂ ++ [zAj])` is an infix of the arc `b_j · G₂ · a_j` of `K` on `Π_j`;
  - `α zAj :: (a.sideFrom j ++ [α zAi])` is an infix of the rotation `S_ai · Ā_aj · S_aj · Ā_ai`
    of the boundary of `a`;
  - `zAi :: (G₁ ++ [zBi])` is an infix of the arc `a_i · G₁ · b_i` of `K` on `Π_i`.
* The four corners bounce (`witnessStepCurve_bounce`); `zBi ∉ G₁` and `zAi ∉ G₁` come from the
  duplicate-free arc `a_i · G₁ · b_i`, likewise on `Π_j`.
So `witnessStepCurve_double_chain` applies.
-/

namespace GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket

universe u w v

open Embedded HullSC WordMetric SimpleClosedWalkSides Surgery.MapCollapse

namespace FourPieceWitness

section Chain

variable {G : Type u} [Group G] {Lambda : Type w} {W : Set (List (RelLetter G Lambda))}
  {D : RelGenSet G Lambda} {eps : ℕ} {X : DiscDiagram.{u, w, v} W} {i j : Fin X.rCellCount}

/-- **U1 for the pocket curve.**  No dart of `Γ` has both faces in `a`, nor both in `b`. -/
theorem witnessStepCurve_pocket_unique {a b : RegionCandidate D eps X} (hab : Disjoint a.1 b.1)
    (hai : (cell X i).face ∉ a.1) (haj : (cell X j).face ∉ a.1) (hbi : (cell X i).face ∉ b.1)
    (hbj : (cell X j).face ∉ b.1) (G₁ : CyclicArc (cellDarts X i))
    (G₂ : CyclicArc (cellDarts X j)) {Γ : List X.toCombMap.Dart}
    (hΓ : Γ = b.sideFrom i ++ G₂.darts ++ a.sideFrom j ++ G₁.darts) :
    (∀ d ∈ Γ, X.toCombMap.faceOf d ∈ b.1 → X.toCombMap.faceOf (X.toCombMap.alpha d) ∉ b.1) ∧
      (∀ d ∈ Γ, X.toCombMap.faceOf d ∈ a.1 → X.toCombMap.faceOf (X.toCombMap.alpha d) ∉ a.1) := by
  have hG₁ : ∀ d ∈ G₁.darts, X.toCombMap.faceOf d = (cell X i).face := fun d hd =>
    faceOf_of_mem_cellDarts (G₁.mem_cycle_of_mem_darts hd)
  have hG₂ : ∀ d ∈ G₂.darts, X.toCombMap.faceOf d = (cell X j).face := fun d hd =>
    faceOf_of_mem_cellDarts (G₂.mem_cycle_of_mem_darts hd)
  refine ⟨witnessStepCurve_unique b i (Γ := Γ) fun d hd => ?_,
    witnessStepCurve_unique a j (Γ := Γ) fun d hd => ?_⟩
  · rw [hΓ] at hd
    simp only [List.mem_append] at hd
    rcases hd with ((hd | hd) | hd) | hd
    · exact Or.inl hd
    · exact Or.inr (by rw [hG₂ d hd]; exact hbj)
    · exact Or.inr
        (Finset.disjoint_left.mp hab (witnessStepCorner_faceOf_mem_of_mem_sideFrom a j hd))
    · exact Or.inr (by rw [hG₁ d hd]; exact hbi)
  · rw [hΓ] at hd
    simp only [List.mem_append] at hd
    rcases hd with ((hd | hd) | hd) | hd
    · exact Or.inr
        (Finset.disjoint_left.mp hab.symm (witnessStepCorner_faceOf_mem_of_mem_sideFrom b i hd))
    · exact Or.inr (by rw [hG₂ d hd]; exact haj)
    · exact Or.inl hd
    · exact Or.inr (by rw [hG₁ d hd]; exact hai)

#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.FourPieceWitness.witnessStepCurve_pocket_unique

/-- **Bounce facts off the pocket curve, for a corner of `b`.** -/
theorem witnessStepCurve_bounce_b {a b : RegionCandidate D eps X}
    {G₁ : CyclicArc (cellDarts X i)} {G₂ : CyclicArc (cellDarts X j)} {Γ : List X.toCombMap.Dart}
    (hΓ : Γ = b.sideFrom i ++ G₂.darts ++ a.sideFrom j ++ G₁.darts) {z : X.toCombMap.Dart}
    (r : (z ∉ b.sideFrom i ∧ z ∉ a.sideFrom j ∧ z ∉ G₁.darts ∧ z ∉ G₂.darts) ∧
      (X.toCombMap.alpha z ∉ b.sideFrom i ∧ X.toCombMap.alpha z ∉ a.sideFrom j ∧
        X.toCombMap.alpha z ∉ G₁.darts ∧ X.toCombMap.alpha z ∉ G₂.darts)) :
    z ∉ Γ ∧ X.toCombMap.alpha z ∉ Γ := by
  rw [hΓ]
  exact ⟨witnessStepCurve_not_mem_four r.1.1 r.1.2.2.2 r.1.2.1 r.1.2.2.1,
    witnessStepCurve_not_mem_four r.2.1 r.2.2.2.2 r.2.2.1 r.2.2.2.1⟩

#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.FourPieceWitness.witnessStepCurve_bounce_b

/-- **Bounce facts off the pocket curve, for a corner of `a`.** -/
theorem witnessStepCurve_bounce_a {a b : RegionCandidate D eps X}
    {G₁ : CyclicArc (cellDarts X i)} {G₂ : CyclicArc (cellDarts X j)} {Γ : List X.toCombMap.Dart}
    (hΓ : Γ = b.sideFrom i ++ G₂.darts ++ a.sideFrom j ++ G₁.darts) {z : X.toCombMap.Dart}
    (r : (z ∉ a.sideFrom j ∧ z ∉ b.sideFrom i ∧ z ∉ G₁.darts ∧ z ∉ G₂.darts) ∧
      (X.toCombMap.alpha z ∉ a.sideFrom j ∧ X.toCombMap.alpha z ∉ b.sideFrom i ∧
        X.toCombMap.alpha z ∉ G₁.darts ∧ X.toCombMap.alpha z ∉ G₂.darts)) :
    z ∉ Γ ∧ X.toCombMap.alpha z ∉ Γ := by
  rw [hΓ]
  exact ⟨witnessStepCurve_not_mem_four r.1.2.1 r.1.2.2.2 r.1.1 r.1.2.2.1,
    witnessStepCurve_not_mem_four r.2.2.1 r.2.2.2.2 r.2.1 r.2.2.2.1⟩

#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.FourPieceWitness.witnessStepCurve_bounce_a

end Chain

end FourPieceWitness

end GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket
