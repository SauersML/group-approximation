import GroupApproximation.GGT.VanKampen.SimpleClosedWalkSides
import GroupApproximation.Meta.AxiomGuard

/-!
# The side faces of a boundary cycle

Osin, arXiv:math/0411039v3, §9, proof of Lemma 9.7(b): the subdiagram `Γ_1` is the part of `Δ`
cut off by the closed walk `s_1 t_1 s_2 t_2`.  The faces on the side of a walk (`sideFaces`) are
those reached from a dart of the walk by advancing around faces and crossing edges off the walk.
When the walk is the boundary cycle of a face set, in a connected map with a face outside the set,
these are exactly the faces of the set.

* `SimpleClosedWalkSides.sideFaces_boundaryCycle_subset`: the faces on the side of a boundary
  cycle lie in the face set.
* `SimpleClosedWalkSides.sideFaces_boundaryCycle_eq`: in a connected map, if some face is not in
  the face set, the side faces are the face set.

Advancing around a face keeps the face, and an edge off the cycle with exactly one face in the set
would be a boundary edge, so the side stays in the set.  Conversely, the faces of the set off the
side are closed under crossing every edge, and a vertex rotation lands on the face across the edge,
so by connectivity they would contain every face, the outside face included.

## Manuscript status

Infrastructure for `thm:hull` (tex 1636, "Hull's small cancellation theorem", through Osin's
Lemma 4.4); certifies no printed sentence on its own.
-/

namespace GroupApproximation.GGT.VanKampen.SimpleClosedWalkSides

open Surgery.MapCollapse

universe u

/-- The vertex rotation of a dart lies on the face across its edge. -/
private theorem faceOf_sigma_eq_faceOf_alpha (M : CombMap.{u}) (d : M.Dart) :
    M.faceOf (M.sigma d) = M.faceOf (M.alpha d) := by
  have h : M.facePerm (M.alpha d) = M.sigma d := by
    show M.sigma (M.alpha (M.alpha d)) = M.sigma d
    rw [M.alpha_involutive d]
  rw [← h, M.faceOf_facePerm]

/-- Crossing an edge that is not on the boundary cycle keeps membership in the face set. -/
theorem faceOf_alpha_mem_iff_of_not_walkKeep {M : CombMap.{u}} {faces : Finset M.Face}
    (boundary : BoundaryCycle M faces) {x : M.Dart} (hx : ¬ walkKeep M boundary.cycle x) :
    M.faceOf (M.alpha x) ∈ faces ↔ M.faceOf x ∈ faces := by
  constructor
  · intro h
    by_contra hn
    refine hx (Or.inr ((boundary.cycle_mem_iff (M.alpha x)).mpr ⟨h, ?_⟩))
    rwa [M.alpha_involutive x]
  · intro h
    by_contra hn
    exact hx (Or.inl ((boundary.cycle_mem_iff x).mpr ⟨h, hn⟩))

/-- Along a face class off the boundary cycle, membership in the face set does not change. -/
theorem faceOf_mem_iff_of_faceClass {M : CombMap.{u}} {faces : Finset M.Face}
    (boundary : BoundaryCycle M faces) {x y : M.Dart}
    (h : Relation.EqvGen (CombMap.FaceClassStep M (walkKeep M boundary.cycle)) x y) :
    M.faceOf x ∈ faces ↔ M.faceOf y ∈ faces := by
  induction h with
  | rel x₁ x₂ hx =>
      rcases hx with rfl | ⟨hk, rfl⟩
      · rw [M.faceOf_facePerm]
      · exact (faceOf_alpha_mem_iff_of_not_walkKeep boundary hk).symm
  | refl x₁ => exact Iff.rfl
  | symm x₁ x₂ _ ih => exact ih.symm
  | trans x₁ x₂ x₃ _ _ ih₁ ih₂ => exact ih₁.trans ih₂

/-- **The faces on the side of a boundary cycle lie in the face set.** -/
theorem sideFaces_boundaryCycle_subset {M : CombMap.{u}} {faces : Finset M.Face}
    (boundary : BoundaryCycle M faces) : sideFaces M boundary.cycle ⊆ faces := by
  intro g hg
  obtain ⟨x, hx⟩ := Quotient.exists_rep g
  have hx' : M.faceOf x = g := hx
  subst hx'
  obtain ⟨d, hd, h⟩ := (mem_sideFaces_iff M boundary.cycle x).mp hg
  exact (faceOf_mem_iff_of_faceClass boundary h).mp ((boundary.cycle_mem_iff d).mp hd).1

/-- A dart on a face of the set that is not on the side of the boundary cycle is not on an edge
of the cycle. -/
theorem not_walkKeep_of_mem_not_mem_sideFaces {M : CombMap.{u}} {faces : Finset M.Face}
    (boundary : BoundaryCycle M faces) {x : M.Dart} (hx : M.faceOf x ∈ faces)
    (hs : M.faceOf x ∉ sideFaces M boundary.cycle) : ¬ walkKeep M boundary.cycle x := by
  rintro (h | h)
  · exact hs ((mem_sideFaces_iff M boundary.cycle x).mpr ⟨x, h, .refl _⟩)
  · have hb := ((boundary.cycle_mem_iff (M.alpha x)).mp h).2
    rw [M.alpha_involutive x] at hb
    exact hb hx

/-- Crossing an edge from a face of the set off the side of the boundary cycle reaches a face of
the set off the side. -/
theorem alpha_mem_not_mem_sideFaces {M : CombMap.{u}} {faces : Finset M.Face}
    (boundary : BoundaryCycle M faces) {x : M.Dart}
    (hx : M.faceOf x ∈ faces ∧ M.faceOf x ∉ sideFaces M boundary.cycle) :
    M.faceOf (M.alpha x) ∈ faces ∧ M.faceOf (M.alpha x) ∉ sideFaces M boundary.cycle := by
  have hk := not_walkKeep_of_mem_not_mem_sideFaces boundary hx.1 hx.2
  refine ⟨(faceOf_alpha_mem_iff_of_not_walkKeep boundary hk).mpr hx.1, fun hs => hx.2 ?_⟩
  obtain ⟨d, hd, h⟩ := (mem_sideFaces_iff M boundary.cycle (M.alpha x)).mp hs
  exact (mem_sideFaces_iff M boundary.cycle x).mpr
    ⟨d, hd, .trans _ _ _ h (.symm _ _ (.rel _ _ (Or.inr ⟨hk, rfl⟩)))⟩

/-- In a connected map, a property of faces that passes across every edge holds at every face
once it holds at one. -/
theorem faceOf_of_alpha_closed {M : CombMap.{u}} (hM : M.IsConnected) {T : M.Face → Prop}
    (hT : ∀ x, T (M.faceOf x) → T (M.faceOf (M.alpha x))) (d e : M.Dart)
    (hd : T (M.faceOf d)) : T (M.faceOf e) := by
  have halpha : ∀ x, T (M.faceOf x) ↔ T (M.faceOf (M.alpha x)) := fun x =>
    ⟨hT x, fun hx => by
      have h := hT (M.alpha x) hx
      rwa [M.alpha_involutive x] at h⟩
  have hgen : ∀ u v, Relation.EqvGen M.Adjacent u v → (T (M.faceOf u) ↔ T (M.faceOf v)) := by
    intro u v h
    induction h with
    | rel u v h =>
        rcases h with rfl | rfl
        · exact halpha u
        · rw [faceOf_sigma_eq_faceOf_alpha M u]
          exact halpha u
    | refl u => exact Iff.rfl
    | symm u v _ ih => exact ih.symm
    | trans u v w _ _ ih₁ ih₂ => exact ih₁.trans ih₂
  exact (hgen d e (hM d e)).mp hd

/-- **The side faces of a boundary cycle are the face set.**  In a connected map with a face `f`
outside `faces`, the faces reached from a boundary cycle of `faces` by advancing around faces and
crossing edges off the cycle are exactly `faces`. -/
theorem sideFaces_boundaryCycle_eq {M : CombMap.{u}} (hM : M.IsConnected) {faces : Finset M.Face}
    (boundary : BoundaryCycle M faces) {f : M.Face} (hf : f ∉ faces) :
    sideFaces M boundary.cycle = faces := by
  refine Finset.Subset.antisymm (sideFaces_boundaryCycle_subset boundary) ?_
  intro g hg
  by_contra hs
  obtain ⟨x, hx⟩ := Quotient.exists_rep g
  have hx' : M.faceOf x = g := hx
  subst hx'
  obtain ⟨y, hy⟩ := Quotient.exists_rep f
  have hy' : M.faceOf y = f := hy
  subst hy'
  exact hf (faceOf_of_alpha_closed hM (T := fun F => F ∈ faces ∧ F ∉ sideFaces M boundary.cycle)
    (fun _ hx => alpha_mem_not_mem_sideFaces boundary hx) x y ⟨hg, hs⟩).1

end GroupApproximation.GGT.VanKampen.SimpleClosedWalkSides

#audit_axioms GroupApproximation.GGT.VanKampen.SimpleClosedWalkSides.sideFaces_boundaryCycle_subset
#audit_axioms GroupApproximation.GGT.VanKampen.SimpleClosedWalkSides.sideFaces_boundaryCycle_eq
