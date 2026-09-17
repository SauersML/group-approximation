import GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P01EmptyTwoGon.ClassInjective
import GroupApproximation.GGT.VanKampen.Estimating.OsinAppendixO52Prep
import GroupApproximation.GGT.VanKampen.Estimating.OsinAppendixSectionMultipleEdge
import GroupApproximation.Meta.AxiomGuard

/-!
# Greendlinger leaf P01, empty two-gons: the faces charged to a selected region

Steps 3 and 4 of the proof in `ClassBasics`.

* `not_contactKeep_of_mem`: a dart based at a face of a selected region is not retained by the
  contact map.  A representative is based at a polygon face (never selected), and the reverse of a
  representative is based at an object face: the exterior (not in a region) or a relator cell, whose
  word has value `≠ 1` in a least-area diagram, while every face of a region has value `1`.
* `contactClass_head_of_mem`: all darts based at the faces of a region lie in one class.  The
  boundary cycle of the region is one class (every boundary step is a class path), and a dart of the
  region outside that class propagates, through `α` and `σ`, to the whole connected diagram, hence to
  the exterior, which lies in no region.
* `RegionHeld P F a`: the class of `F` reaches a dart based at a face of `a`.
* `card_regionHeld_le`: a region charges at most one face holding no object (`regionHeld_unique`,
  from `faceOf_eq_of_not_holdsObject`), so these faces number at most `#S.family`.

## Manuscript status

Infrastructure for `thm:hull` (through Osin's Lemma 9.4); certifies no printed sentence on its own.
-/

namespace GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P01EmptyTwoGon

universe u w v

open GroupApproximation.GGT.VanKampen.Embedded
open GroupApproximation.GGT.VanKampen.UnboundEstimate
open scoped Classical

section RegionCharge

variable {G : Type u} [Group G] {Lambda : Type w} {W : Set (List (RelLetter G Lambda))}
  {D : RelGenSet G Lambda} {lambda c : ℝ} {eps : ℕ} {Delta : DiscDiagram.{u, w, v} W}
  {cuts : SectionCuts D lambda c Delta.boundaryWord}
  {S : GloballyDistinguishedSectionFamily D lambda c eps Delta cuts}

/-- **Step 3a: a dart based at a face of a selected region is not retained.** -/
theorem not_contactKeep_of_mem (P : OsinLemma94RealizedPolygons S) (hleast : Delta.LeastArea)
    {a : RegionCandidate D eps S.diagram} (ha : a ∈ S.family) {d : S.diagram.toCombMap.Dart}
    (hd : S.diagram.toCombMap.faceOf d ∈ a.1) : ¬ P.ContactKeep d := by
  rintro (⟨k, o, h, -, rfl⟩ | ⟨k, o, h, -, hx⟩)
  · rw [P.faceOf_rep] at hd
    exact P.face_unselected k a ha hd
  · have e := P.faceOf_alpha_rep k o h
    rw [← hx, S.diagram.toCombMap.alpha_involutive d] at e
    rw [e] at hd
    cases o with
    | none => exact (a.2.boundary.all_gCells _ hd).1 rfl
    | some j =>
      refine DiscDiagram.leastArea_listVal_word_ne_one (S.equiv.leastArea hleast)
        (Embedded.cell S.diagram j) (Embedded.cell_mem S.diagram j) ?_
      rw [S.diagram.relatorCell_word _ (Embedded.cell_mem S.diagram j)]
      exact (a.2.boundary.all_gCells _ hd).2

/-- Internal boundary moves are class paths (vertex rotations of the dual). -/
theorem contactClass_of_internal (P : OsinLemma94RealizedPolygons S)
    {faces : Finset S.diagram.toCombMap.Face} {d e : S.diagram.toCombMap.Dart}
    (h : Relation.ReflTransGen (Embedded.InternalBoundaryMove S.diagram faces) d e) :
    ContactClass P d e := by
  induction h with
  | refl => exact Relation.EqvGen.refl _
  | tail _ hmove ih =>
    obtain ⟨-, -, rfl⟩ := hmove
    rw [facePerm_alpha_eq_sigma]
    exact Relation.EqvGen.trans _ _ _ ih
      (faceClass_dual_sigma S.diagram.toCombMap P.ContactKeep _)

/-- A boundary step of a selected region is a class path. -/
theorem contactClass_of_boundaryStep (P : OsinLemma94RealizedPolygons S)
    (hleast : Delta.LeastArea) {a : RegionCandidate D eps S.diagram} (ha : a ∈ S.family)
    {d e : S.diagram.toCombMap.Dart} (h : Embedded.BoundaryStep S.diagram a.1 d e) :
    ContactClass P d e :=
  Relation.EqvGen.trans _ _ _
    (faceClass_dual_facePerm S.diagram.toCombMap P.ContactKeep
      (not_contactKeep_of_mem P hleast ha h.1.1))
    (contactClass_of_internal P h.2.2)

/-- The base dart of a region: the head of its boundary cycle. -/
abbrev regionBase (a : RegionCandidate D eps S.diagram) : S.diagram.toCombMap.Dart :=
  a.2.boundary.cycle.head a.2.boundary.cycle_nonempty

/-- The boundary cycle of a selected region lies in the class of its base dart. -/
theorem contactClass_head_cycle (P : OsinLemma94RealizedPolygons S) (hleast : Delta.LeastArea)
    {a : RegionCandidate D eps S.diagram} (ha : a ∈ S.family) :
    ∀ d ∈ a.2.boundary.cycle, ContactClass P (regionBase a) d :=
  List.IsChain.induction (fun d => ContactClass P (regionBase a) d) a.2.boundary.cycle
    a.2.boundary.cycle_chain
    (by
      intro _ _ hstep hx
      exact Relation.EqvGen.trans _ _ _ hx (contactClass_of_boundaryStep P hleast ha hstep))
    (fun _ => Relation.EqvGen.refl _)

/-- Outside the base class, a dart of a region crosses its edge into the region. -/
theorem region_alpha (P : OsinLemma94RealizedPolygons S) (hleast : Delta.LeastArea)
    {a : RegionCandidate D eps S.diagram} (ha : a ∈ S.family) {x : S.diagram.toCombMap.Dart}
    (hx : S.diagram.toCombMap.faceOf x ∈ a.1) (hno : ¬ ContactClass P (regionBase a) x) :
    S.diagram.toCombMap.faceOf (S.diagram.toCombMap.alpha x) ∈ a.1 ∧
      ¬ ContactClass P (regionBase a) (S.diagram.toCombMap.alpha x) := by
  have hxα : S.diagram.toCombMap.faceOf (S.diagram.toCombMap.alpha x) ∈ a.1 := by
    by_contra hout
    exact hno (contactClass_head_cycle P hleast ha x ((a.2.boundary.cycle_mem_iff x).mpr ⟨hx, hout⟩))
  exact ⟨hxα, fun h => hno (Relation.EqvGen.trans _ _ _ h (Relation.EqvGen.symm _ _
    (faceClass_dual_alpha S.diagram.toCombMap P.ContactKeep (not_contactKeep_of_mem P hleast ha hx))))⟩

/-- `region_alpha`, read backwards. -/
theorem region_alpha_back (P : OsinLemma94RealizedPolygons S) (hleast : Delta.LeastArea)
    {a : RegionCandidate D eps S.diagram} (ha : a ∈ S.family) {x : S.diagram.toCombMap.Dart}
    (hx : S.diagram.toCombMap.faceOf (S.diagram.toCombMap.alpha x) ∈ a.1)
    (hno : ¬ ContactClass P (regionBase a) (S.diagram.toCombMap.alpha x)) :
    S.diagram.toCombMap.faceOf x ∈ a.1 ∧ ¬ ContactClass P (regionBase a) x := by
  have h := region_alpha P hleast ha hx hno
  rwa [S.diagram.toCombMap.alpha_involutive x] at h

/-- Outside the base class, a dart of a region rotates at its vertex into the region. -/
theorem region_sigma (P : OsinLemma94RealizedPolygons S) (hleast : Delta.LeastArea)
    {a : RegionCandidate D eps S.diagram} (ha : a ∈ S.family) {x : S.diagram.toCombMap.Dart}
    (hx : S.diagram.toCombMap.faceOf x ∈ a.1) (hno : ¬ ContactClass P (regionBase a) x) :
    S.diagram.toCombMap.faceOf (S.diagram.toCombMap.sigma x) ∈ a.1 ∧
      ¬ ContactClass P (regionBase a) (S.diagram.toCombMap.sigma x) := by
  have hxα := (region_alpha P hleast ha hx hno).1
  refine ⟨?_, fun h => hno (Relation.EqvGen.trans _ _ _ h (Relation.EqvGen.symm _ _
    (faceClass_dual_sigma S.diagram.toCombMap P.ContactKeep x)))⟩
  rw [← facePerm_alpha_eq_sigma S.diagram.toCombMap x, S.diagram.toCombMap.faceOf_facePerm]
  exact hxα

/-- `region_sigma`, read backwards. -/
theorem region_sigma_back (P : OsinLemma94RealizedPolygons S) (hleast : Delta.LeastArea)
    {a : RegionCandidate D eps S.diagram} (ha : a ∈ S.family) {x : S.diagram.toCombMap.Dart}
    (hx : S.diagram.toCombMap.faceOf (S.diagram.toCombMap.sigma x) ∈ a.1)
    (hno : ¬ ContactClass P (regionBase a) (S.diagram.toCombMap.sigma x)) :
    S.diagram.toCombMap.faceOf x ∈ a.1 ∧ ¬ ContactClass P (regionBase a) x := by
  have hαx : S.diagram.toCombMap.faceOf (S.diagram.toCombMap.alpha x) ∈ a.1 := by
    rw [← S.diagram.toCombMap.faceOf_facePerm (S.diagram.toCombMap.alpha x),
      facePerm_alpha_eq_sigma]
    exact hx
  have hstep : ContactClass P (S.diagram.toCombMap.alpha x) (S.diagram.toCombMap.sigma x) := by
    have h := faceClass_dual_facePerm S.diagram.toCombMap P.ContactKeep
      (not_contactKeep_of_mem P hleast ha hαx)
    rwa [facePerm_alpha_eq_sigma] at h
  exact region_alpha_back P hleast ha hαx (fun h => hno (Relation.EqvGen.trans _ _ _ h hstep))

/-- **Step 3b: the darts of a selected region lie in one class.** -/
theorem contactClass_head_of_mem (P : OsinLemma94RealizedPolygons S) (hleast : Delta.LeastArea)
    {a : RegionCandidate D eps S.diagram} (ha : a ∈ S.family) {d : S.diagram.toCombMap.Dart}
    (hd : S.diagram.toCombMap.faceOf d ∈ a.1) : ContactClass P (regionBase a) d := by
  by_contra hno
  obtain ⟨y, hy⟩ := Quotient.exists_rep S.diagram.outerFace
  have hB := invariant_of_isConnected S.diagram.toCombMap
    (S.diagram.toCombMap.connected_of_planar S.diagram.planar)
    (fun x => S.diagram.toCombMap.faceOf x ∈ a.1 ∧ ¬ ContactClass P (regionBase a) x)
    (fun _ => ⟨fun h => region_alpha P hleast ha h.1 h.2,
      fun h => region_alpha_back P hleast ha h.1 h.2⟩)
    (fun _ => ⟨fun h => region_sigma P hleast ha h.1 h.2,
      fun h => region_sigma_back P hleast ha h.1 h.2⟩)
    d y ⟨hd, hno⟩
  have hyo : S.diagram.toCombMap.faceOf y = S.diagram.outerFace := hy
  exact (a.2.boundary.all_gCells _ hB.1).1 hyo

/-- A face of the contact map is **held by a region** when its class reaches a dart of the region. -/
def RegionHeld (P : OsinLemma94RealizedPolygons S) (F : P.contactMap.Face)
    (a : RegionCandidate D eps S.diagram) : Prop :=
  ∃ x : P.contactMap.Dart, P.contactMap.faceOf x = F ∧
    ∃ y : S.diagram.toCombMap.Dart, ContactClass P x.1 y ∧ S.diagram.toCombMap.faceOf y ∈ a.1

/-- **Step 4a: a region holds at most one face holding no object.** -/
theorem regionHeld_unique (P : OsinLemma94RealizedPolygons S) (hleast : Delta.LeastArea)
    {a : RegionCandidate D eps S.diagram} (ha : a ∈ S.family) {F₁ F₂ : P.contactMap.Face}
    (h₁ : ¬ P.HoldsObject F₁) (hr₁ : RegionHeld P F₁ a) (hr₂ : RegionHeld P F₂ a) : F₁ = F₂ := by
  obtain ⟨x₁, hx₁, y₁, hxy₁, hy₁⟩ := hr₁
  obtain ⟨x₂, hx₂, y₂, hxy₂, hy₂⟩ := hr₂
  have hc : ContactClass P x₁.1 x₂.1 :=
    Relation.EqvGen.trans _ _ _
      (Relation.EqvGen.trans _ _ _ hxy₁
        (Relation.EqvGen.symm _ _ (contactClass_head_of_mem P hleast ha hy₁)))
      (Relation.EqvGen.trans _ _ _ (contactClass_head_of_mem P hleast ha hy₂)
        (Relation.EqvGen.symm _ _ hxy₂))
  exact (faceOf_eq_of_not_holdsObject P h₁ hx₁ hc).symm.trans hx₂

/-- **Step 4b: the faces holding no object but held by a region number at most `#S.family`.** -/
theorem card_regionHeld_le (P : OsinLemma94RealizedPolygons S) (hleast : Delta.LeastArea) :
    (Finset.univ.filter fun F : P.contactMap.Face =>
      ¬ P.HoldsObject F ∧ ∃ a ∈ S.family, RegionHeld P F a).card ≤ S.family.card := by
  refine Finset.card_le_card_of_forall_subsingleton (fun F a => RegionHeld P F a) ?_ ?_
  · intro F hF
    obtain ⟨-, a, ha, hr⟩ := (Finset.mem_filter.mp hF).2
    exact ⟨a, ha, hr⟩
  · rintro a ha F₁ ⟨hF₁, hr₁⟩ F₂ ⟨-, hr₂⟩
    have h1 : F₁ ∈ (Finset.univ.filter fun F : P.contactMap.Face =>
        ¬ P.HoldsObject F ∧ ∃ a ∈ S.family, RegionHeld P F a) := hF₁
    exact regionHeld_unique P hleast ha (Finset.mem_filter.mp h1).2.1 hr₁ hr₂

end RegionCharge

end GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P01EmptyTwoGon

#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P01EmptyTwoGon.contactClass_head_of_mem
#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P01EmptyTwoGon.card_regionHeld_le
