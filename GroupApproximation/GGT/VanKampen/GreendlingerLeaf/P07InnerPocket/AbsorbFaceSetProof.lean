import GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.AbsorbFaceSetStatement
import GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.AbsorbFaceSetIterate
import GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.NoWalkAbsorbLemmas
import GroupApproximation.Meta.AxiomGuard

/-!
# Greendlinger leaf P07, lane gl-p07-38: the target from the absorption iteration

* `FourPieceWitness.absorbFaceSet_exposed_of_not_stepGood`: if the four step clauses fail for an
  enclosed successor walk, some gap dart is exposed.  Otherwise both gaps are closed, and
  `noWalkAbsorb_step_of_closed` and `noWalkAbsorb_unique_of_closed` give the step clauses.  The face
  across the exposed successor is outside `F` by `mem_iff`, and it is inside the pocket because
  gap darts reverse onto `K.walk`.
* `FourPieceWitness.noPlanarDegenStep_of_absorbFaceSet`: `AbsorbFaceSetStatement` implies
  `NoPlanarDegenStepStatement`, through `absorbFaceSet_iterate`.
* `FourPieceWitness.absorbFaceSet_of_noPlanarDegenStep` and
  `FourPieceWitness.absorbFaceSet_iff_noPlanarDegenStep`: the converse, and the equivalence.

## LOUD: EQUIVALENT to the target

See the docstring of `AbsorbFaceSetStatement.lean`.  The statement is smaller in proof content,
not weaker as a `Prop`.
-/

namespace GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket

universe u w v

open Embedded HullSC WordMetric SimpleClosedWalkSides Surgery.MapCollapse

namespace FourPieceWitness

section Exposed

variable {G : Type u} [Group G] {Lambda : Type w} {W : Set (List (RelLetter G Lambda))}
  {D : RelGenSet G Lambda} {eps : ℕ} {X : DiscDiagram.{u, w, v} W} {i j : Fin X.rCellCount}

/-- **Failing step clauses expose a gap dart.** -/
theorem absorbFaceSet_exposed_of_not_stepGood (K : CellPocketWalk D eps X i j)
    {G₁ : CyclicArc (cellDarts X i)} {G₂ : CyclicArc (cellDarts X j)}
    {pre₁ post₁ pre₂ post₂ : List X.toCombMap.Dart}
    (hG₁ : K.firstArc.darts = pre₁ ++ G₁.darts ++ post₁)
    (hG₂ : K.secondArc.darts = pre₂ ++ G₂.darts ++ post₂)
    {F : Finset X.toCombMap.Face} {ow : List X.toCombMap.Dart} (E : EnclosedFaceSetSucc X F ow)
    (hS : ¬ AbsorbFaceSetStepGood G₁ G₂ ow) : AbsorbFaceSetExposed K G₁ G₂ F ow := by
  have hexp : ∀ g ∈ ow, ((g ∈ G₁.darts ∧ X.toCombMap.facePerm g ∈ G₁.darts) ∨
      (g ∈ G₂.darts ∧ X.toCombMap.facePerm g ∈ G₂.darts)) →
      X.toCombMap.facePerm g ∉ ow → AbsorbFaceSetExposed K G₁ G₂ F ow := by
    intro g hg hgap hfg
    have hface : X.toCombMap.faceOf (X.toCombMap.facePerm g) ∉ F := by
      rw [X.toCombMap.faceOf_facePerm g]
      exact ((E.mem_iff g).mp hg).1
    have hnot : ¬ (X.toCombMap.faceOf (X.toCombMap.alpha (X.toCombMap.facePerm g)) ∈ F ∨
        X.toCombMap.alpha (X.toCombMap.facePerm g) ∈ ow) :=
      fun h => hfg ((E.mem_iff (X.toCombMap.facePerm g)).mpr ⟨hface, h⟩)
    have hwalk : X.toCombMap.alpha (X.toCombMap.facePerm g) ∈ K.walk := by
      rcases hgap with ⟨-, hf⟩ | ⟨-, hf⟩
      · have hx : X.toCombMap.alpha (X.toCombMap.facePerm g) ∈ invDarts X G₁.darts := by
          rw [Embedded.mem_invDarts_iff, X.toCombMap.alpha_involutive (X.toCombMap.facePerm g)]
          exact hf
        exact noWalkAbsorb_mem_walk_of_first K hG₁ hx
      · have hx : X.toCombMap.alpha (X.toCombMap.facePerm g) ∈ invDarts X G₂.darts := by
          rw [Embedded.mem_invDarts_iff, X.toCombMap.alpha_involutive (X.toCombMap.facePerm g)]
          exact hf
        exact noWalkAbsorb_mem_walk_of_second K hG₂ hx
    exact ⟨g, hg, hgap, hfg, fun h => hnot (Or.inr h), fun h => hnot (Or.inl h),
      (mem_sideFaces_iff X.toCombMap K.walk (X.toCombMap.alpha (X.toCombMap.facePerm g))).mpr
        ⟨_, hwalk, Relation.EqvGen.refl _⟩⟩
  by_contra hne
  have hcl₁ : ∀ g ∈ G₁.darts, g ∈ ow → X.toCombMap.facePerm g ∈ G₁.darts →
      X.toCombMap.facePerm g ∈ ow := by
    intro g hg1 hg hf
    by_contra hfg
    exact hne (hexp g hg (Or.inl ⟨hg1, hf⟩) hfg)
  have hcl₂ : ∀ g ∈ G₂.darts, g ∈ ow → X.toCombMap.facePerm g ∈ G₂.darts →
      X.toCombMap.facePerm g ∈ ow := by
    intro g hg2 hg hf
    by_contra hfg
    exact hne (hexp g hg (Or.inr ⟨hg2, hf⟩) hfg)
  exact hS ⟨fun hoff => noWalkAbsorb_step_of_closed E i G₁ hcl₁ hoff,
    fun hall => noWalkAbsorb_unique_of_closed E i G₁ hcl₁ hall,
    fun hoff => noWalkAbsorb_step_of_closed E j G₂ hcl₂ hoff,
    fun hall => noWalkAbsorb_unique_of_closed E j G₂ hcl₂ hall⟩

#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.FourPieceWitness.absorbFaceSet_exposed_of_not_stepGood

/-- **A basic pair with failing step clauses has an exposed gap dart.** -/
theorem absorbFaceSet_exposed_of_basic {a b : RegionCandidate D eps X}
    (K : CellPocketWalk D eps X i j) {G₁ : CyclicArc (cellDarts X i)}
    {G₂ : CyclicArc (cellDarts X j)}
    (hG₁ : K.firstArc.darts = a.cellArcList i ++ G₁.darts ++ b.cellArcList i)
    (hG₂ : K.secondArc.darts = b.cellArcList j ++ G₂.darts ++ a.cellArcList j)
    {c : X.toCombMap.Face} {F : Finset X.toCombMap.Face} {ow : List X.toCombMap.Dart}
    (hB : AbsorbFaceSetBasic a b K G₁ G₂ c F ow) (hS : ¬ AbsorbFaceSetStepGood G₁ G₂ ow) :
    AbsorbFaceSetExposed K G₁ G₂ F ow := by
  obtain ⟨E, -⟩ := hB
  exact absorbFaceSet_exposed_of_not_stepGood K hG₁ hG₂ E hS

#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.FourPieceWitness.absorbFaceSet_exposed_of_basic

end Exposed

/-- **The target from the absorption iteration.**  See the module docstring. -/
theorem noPlanarDegenStep_of_absorbFaceSet (h : AbsorbFaceSetStatement.{u, w, v}) :
    NoPlanarDegenStepStatement.{u, w, v} := by
  intro G _ Lambda W D eps X i j a b K hij hai hbj hdisj hlet hW hK1 hK2 G₁ hG₁ G₂ hG₂ hw
    hout hinE houtE C hC hCf hCa hCb hno hnc
  obtain ⟨hbase, himp⟩ := h D eps X a b K hij hai hbj hdisj hlet hW hK1 hK2 G₁ hG₁ G₂ hG₂ hw
    hout hinE houtE C hC hCf hCa hCb hno hnc
  rcases absorbFaceSet_iterate (β := X.toCombMap.Face) (γ := List X.toCombMap.Dart)
      (B := fun F ow => AbsorbFaceSetBasic a b K G₁ G₂ C.face F ow)
      (S := fun _ ow => AbsorbFaceSetStepGood G₁ G₂ ow)
      (R := AbsorbFaceSetBranchTwo i j C.face) hbase
      (fun F ow hB hS => himp F ow hB hS (absorbFaceSet_exposed_of_basic K hG₁ hG₂ hB hS)) with
    ⟨F, ow, ⟨E, hc, hsub, hd, h1, h2, h3, h4⟩, s1, s2, s3, s4⟩ | hR
  · exact Or.inl ⟨F, ow, E, hc, hsub, hd, h1, h2, h3, h4, s1, s2, s3, s4⟩
  · exact Or.inr hR

#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.FourPieceWitness.noPlanarDegenStep_of_absorbFaceSet

/-- **The converse.**  A good pair of the target serves Base and every Improve step, and branch 2
serves both parts. -/
theorem absorbFaceSet_of_noPlanarDegenStep (h : NoPlanarDegenStepStatement.{u, w, v}) :
    AbsorbFaceSetStatement.{u, w, v} := by
  intro G _ Lambda W D eps X i j a b K hij hai hbj hdisj hlet hW hK1 hK2 G₁ hG₁ G₂ hG₂ hw
    hout hinE houtE C hC hCf hCa hCb hno hnc
  rcases h D eps X a b K hij hai hbj hdisj hlet hW hK1 hK2 G₁ hG₁ G₂ hG₂ hw hout hinE houtE C hC
      hCf hCa hCb hno hnc with
    ⟨F, ow, E, hc, hsub, hd, h1, h2, h3, h4, s1, s2, s3, s4⟩ | hR
  · exact ⟨Or.inl ⟨F, ow, E, hc, hsub, hd, h1, h2, h3, h4⟩,
      fun _ _ _ _ _ => Or.inl ⟨F, ow, ⟨E, hc, hsub, hd, h1, h2, h3, h4⟩,
        Or.inr ⟨s1, s2, s3, s4⟩⟩⟩
  · exact ⟨Or.inr hR, fun _ _ _ _ _ => Or.inr hR⟩

#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.FourPieceWitness.absorbFaceSet_of_noPlanarDegenStep

/-- **The absorption iteration and the target are equivalent.** -/
theorem absorbFaceSet_iff_noPlanarDegenStep :
    AbsorbFaceSetStatement.{u, w, v} ↔ NoPlanarDegenStepStatement.{u, w, v} :=
  ⟨noPlanarDegenStep_of_absorbFaceSet, absorbFaceSet_of_noPlanarDegenStep⟩

#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.FourPieceWitness.absorbFaceSet_iff_noPlanarDegenStep

end FourPieceWitness

end GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket
