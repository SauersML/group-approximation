import GroupApproximation.GGT.VanKampen.GreendlingerLeaf.Piece10Live.ExtremalJordanPickThree
import GroupApproximation.Meta.AxiomGuard

/-!
# The Three statement from the Euler core

Osin, arXiv:math/0411039v3, §9, proof of Lemma 9.7(b).  Lane gl-p10-38.

`extremalJordanPickThree_three_of_twoOutside` proves `ExtremalJordanPickRegionThreeStatement`
(lane gl-p10-35) from the Euler core `ExtremalJordanPickThreeTwoOutsideStatement`.

* A tight passage is not a non-first turn (`extremalJordanPickThree_not_nonFirst_of_tight`).
* A step inside the target arc, or inside the reversed source arc, is a tight passage of the
  boundary cycle.  So it is a core step (`extremalJordanPickThree_step_of_target`,
  `extremalJordanPickThree_step_of_invSource`).
* Hence `ExtremalJordanPickRegionLinked` and `ExtremalJordanPickThreeLinked` are the same relation
  (`extremalJordanPickThree_linked_of_region`, `extremalJordanPickThree_region_of_linked`).
* Not-A gives at most two outside classes (`extremalJordanPickThree_twoOutside_of_covered`).

**LOUD.**  The residual `ExtremalJordanPickThreeTwoOutsideStatement` is logically STRONGER than the
Three statement and strictly smaller in proof content (see `Piece10Live/ExtremalJordanPickThree`).

## Mathematical infrastructure

Infrastructure for `thm:hull` (Hull's small cancellation theorem, through Osin's Lemma 9.7(b));
no manuscript citation of its own.
-/

namespace GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10ExtremalRegion

universe u w v

open Embedded Surgery.MapCollapse SimpleClosedWalkSides P10Rose.FilterMove P10Rose.SubArcMove

section PickThreeReduction

variable {G : Type u} [Group G] {Lambda : Type w} {W : Set (List (RelLetter G Lambda))}
  {D : RelGenSet G Lambda} {eps : ℕ} {X : DiscDiagram.{u, w, v} W} {lo hi : ℕ}

/-- **A tight passage is a first turn.** -/
theorem extremalJordanPickThree_not_nonFirst_of_tight (K : PocketFaceSet D eps X lo hi)
    {d : X.toCombMap.Dart} (hd : d ∈ K.boundary.cycle)
    (ht : P10RegionMove.RegionMoveCoreCloseTight K d hd) :
    ¬P10ChordLift.NonFirstTurn K d hd :=
  fun hnf => hnf (P10RegionMove.regionMoveCoreClose_firstTurn_of_sigma ht)

/-- **A step inside the target arc is a core step.** -/
theorem extremalJordanPickThree_step_of_target (K : PocketFaceSet D eps X lo hi)
    {x y : X.toCombMap.Dart} {l₁ l₂ : List X.toCombMap.Dart}
    (e : K.targetArc.darts = l₁ ++ x :: y :: l₂) : ExtremalJordanPickThreeStep K x y := by
  have h : [x, y] <:+: K.targetArc.darts := ⟨l₁, l₂, by rw [e]; simp⟩
  have hc : [x, y] <:+: K.boundary.cycle := h.trans K.targetArc_infix
  have hxy : x ∈ [x, y] := by simp
  have hx : x ∈ K.boundary.cycle := hc.subset hxy
  unfold ExtremalJordanPickThreeStep
  exact Or.inr ⟨hx, (OuterPinchCornerFix.next_eq_of_infix K.boundary.cycle_nodup hc hx).symm,
    extremalJordanPickThree_not_nonFirst_of_tight K hx
      (P10RegionMove.regionMoveLoose_tight_of_infix_targetArc K h hx)⟩

/-- **A step inside the reversed source arc is a core step.** -/
theorem extremalJordanPickThree_step_of_invSource (K : PocketFaceSet D eps X lo hi)
    {x y : X.toCombMap.Dart} {l₁ l₂ : List X.toCombMap.Dart}
    (e : invDarts X K.sourceArc.darts = l₁ ++ x :: y :: l₂) :
    ExtremalJordanPickThreeStep K x y := by
  have h : [x, y] <:+: invDarts X K.sourceArc.darts := ⟨l₁, l₂, by rw [e]; simp⟩
  have hc : [x, y] <:+: K.boundary.cycle := h.trans K.invDarts_sourceArc_infix
  have hxy : x ∈ [x, y] := by simp
  have hx : x ∈ K.boundary.cycle := hc.subset hxy
  unfold ExtremalJordanPickThreeStep
  exact Or.inr ⟨hx, (OuterPinchCornerFix.next_eq_of_infix K.boundary.cycle_nodup hc hx).symm,
    extremalJordanPickThree_not_nonFirst_of_tight K hx
      (P10RegionMove.regionMoveLoose_tight_of_infix_sourceArc K h hx)⟩

/-- **Linked darts are core-linked**: every linking step of `ExtremalJordanPickRegionStep` is a
core step. -/
theorem extremalJordanPickThree_linked_of_region (K : PocketFaceSet D eps X lo hi)
    {x y : X.toCombMap.Dart} (h : ExtremalJordanPickRegionLinked K x y) :
    ExtremalJordanPickThreeLinked K x y := by
  unfold ExtremalJordanPickRegionLinked at h
  unfold ExtremalJordanPickThreeLinked
  induction h with
  | rel a b hab =>
      refine Relation.EqvGen.rel _ _ ?_
      unfold ExtremalJordanPickRegionStep at hab
      rcases hab with hab | hab | ⟨l₁, l₂, e⟩ | ⟨l₁, l₂, e⟩
      · exact Or.inl hab
      · exact Or.inr hab
      · exact extremalJordanPickThree_step_of_target K e
      · exact extremalJordanPickThree_step_of_invSource K e
  | refl a => exact Relation.EqvGen.refl _
  | symm a b _ ih => exact Relation.EqvGen.symm _ _ ih
  | trans a b c _ _ ih₁ ih₂ => exact Relation.EqvGen.trans _ _ _ ih₁ ih₂

/-- **Core-linked darts are linked**: every core step is a linking step. -/
theorem extremalJordanPickThree_region_of_linked (K : PocketFaceSet D eps X lo hi)
    {x y : X.toCombMap.Dart} (h : ExtremalJordanPickThreeLinked K x y) :
    ExtremalJordanPickRegionLinked K x y := by
  unfold ExtremalJordanPickThreeLinked at h
  unfold ExtremalJordanPickRegionLinked
  induction h with
  | rel a b hab =>
      refine Relation.EqvGen.rel _ _ ?_
      unfold ExtremalJordanPickThreeStep at hab
      unfold ExtremalJordanPickRegionStep
      rcases hab with hab | hab
      · exact Or.inl hab
      · exact Or.inr (Or.inl hab)
  | refl a => exact Relation.EqvGen.refl _
  | symm a b _ ih => exact Relation.EqvGen.symm _ _ ih
  | trans a b c _ _ ih₁ ih₂ => exact Relation.EqvGen.trans _ _ _ ih₁ ih₂

/-- **Not-A gives at most two outside classes**: those of a dart on the exterior face and of a
dart on the source face. -/
theorem extremalJordanPickThree_twoOutside_of_covered (K : PocketFaceSet D eps X lo hi)
    (h : ExtremalJordanPickRegionOutsideCovered K) : ExtremalJordanPickThreeTwoOutside K := by
  unfold ExtremalJordanPickRegionOutsideCovered at h
  obtain ⟨o, ho⟩ : ∃ o, X.toCombMap.faceOf o = X.outerFace := Quotient.exists_rep X.outerFace
  obtain ⟨s, hs⟩ : ∃ s, X.toCombMap.faceOf s = (cell X K.source).face :=
    Quotient.exists_rep (cell X K.source).face
  unfold ExtremalJordanPickThreeTwoOutside
  refine ⟨o, s, fun r hr => ?_⟩
  rcases h r hr with ⟨x, hx, hrx⟩ | ⟨x, hx, hrx⟩
  · exact Or.inl (Relation.EqvGen.trans _ _ _ hrx
      (extremalJordanPickRegion_eqvGen_of_face K (hx.trans ho.symm)))
  · exact Or.inr (Relation.EqvGen.trans _ _ _ hrx
      (extremalJordanPickRegion_eqvGen_of_face K (hx.trans hs.symm)))

end PickThreeReduction

/-- **The endpoint**: the Euler core gives the Three statement. -/
theorem extremalJordanPickThree_three_of_twoOutside
    (h : ExtremalJordanPickThreeTwoOutsideStatement.{u, w, v}) :
    ExtremalJordanPickRegionThreeStatement.{u, w, v} := by
  intro _ _ _ _ D eps X lo hi hhi hla hlabel K hK hft hsrc htgt hpin hrose hcov
  obtain ⟨r₁, h₁, r₂, h₂, r₃, h₃, h₁₂, h₁₃, h₂₃⟩ :=
    h D eps X lo hi hhi hla hlabel K hK hft hsrc htgt hpin hrose
      (extremalJordanPickThree_twoOutside_of_covered K hcov)
  exact ⟨r₁, h₁, r₂, h₂, r₃, h₃,
    fun h' => h₁₂ (extremalJordanPickThree_linked_of_region K h'),
    fun h' => h₁₃ (extremalJordanPickThree_linked_of_region K h'),
    fun h' => h₂₃ (extremalJordanPickThree_linked_of_region K h')⟩

end GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10ExtremalRegion

#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10ExtremalRegion.extremalJordanPickThree_not_nonFirst_of_tight
#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10ExtremalRegion.extremalJordanPickThree_step_of_target
#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10ExtremalRegion.extremalJordanPickThree_step_of_invSource
#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10ExtremalRegion.extremalJordanPickThree_linked_of_region
#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10ExtremalRegion.extremalJordanPickThree_region_of_linked
#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10ExtremalRegion.extremalJordanPickThree_twoOutside_of_covered
#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10ExtremalRegion.extremalJordanPickThree_three_of_twoOutside
