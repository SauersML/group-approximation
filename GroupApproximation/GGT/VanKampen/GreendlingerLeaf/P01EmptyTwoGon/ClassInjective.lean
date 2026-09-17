import GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P01EmptyTwoGon.ClassBasics
import GroupApproximation.GGT.VanKampen.Estimating.OsinLemma94ContactMapHolds
import GroupApproximation.Meta.AxiomGuard

/-!
# Greendlinger leaf P01, empty two-gons: a face holding no object is determined by its class

Step 2 of the proof in `ClassBasics`.  Let `F` be a face of `contactMap P` holding no object, `x₁` a
dart of `F`, and `x₂` a dart of the contact map in the face class of `x₁` (in the dual of the optimal
diagram, off the retained edges).  Then `x₂` lies on `F` (`faceOf_eq_of_not_holdsObject`).

* `exists_colour_false`: every face of the contact map has a dart of colour `false` in the class of
  any of its darts (`faceClass_restriction_facePerm`, `contactColour_sigma`, `contactColour_alpha`).
* The dart `z` of colour `false` is based at an object face `objectFace S o`; since `F` holds no
  object, some dart `z′` of `F` is based at the same face.  So `x₁` and `z` are in one component of
  the contact map, and the separation theorem `faceOf_eq_of_faceClass_of_componentOf` applies.

## Manuscript status

Infrastructure for `thm:hull` (through Osin's Lemma 9.4); certifies no printed sentence on its own.
-/

namespace GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P01EmptyTwoGon

universe u w v

open GroupApproximation.GGT.VanKampen.Embedded
open GroupApproximation.GGT.VanKampen.UnboundEstimate
open scoped Classical

section ClassInjective

variable {G : Type u} [Group G] {Lambda : Type w} {W : Set (List (RelLetter G Lambda))}
  {D : RelGenSet G Lambda} {lambda c : ℝ} {eps : ℕ} {Delta : DiscDiagram.{u, w, v} W}
  {cuts : SectionCuts D lambda c Delta.boundaryWord}
  {S : GloballyDistinguishedSectionFamily D lambda c eps Delta cuts}

/-- The face class of the dual of the optimal diagram, off the retained edges of the contact map. -/
abbrev ContactClass (P : OsinLemma94RealizedPolygons S) :
    S.diagram.toCombMap.Dart → S.diagram.toCombMap.Dart → Prop :=
  Relation.EqvGen (CombMap.FaceClassStep S.diagram.toCombMap.dual P.ContactKeep)

/-- **Every face has a dart of colour `false` in the class of any of its darts.** -/
theorem exists_colour_false (P : OsinLemma94RealizedPolygons S) (x : P.contactMap.Dart) :
    ∃ z : P.contactMap.Dart, P.contactMap.faceOf z = P.contactMap.faceOf x ∧
      P.contactColour z = false ∧ ContactClass P x.1 z.1 := by
  cases hx : P.contactColour x with
  | false => exact ⟨x, rfl, hx, Relation.EqvGen.refl _⟩
  | true =>
    refine ⟨P.contactMap.facePerm x, P.contactMap.faceOf_facePerm x, ?_, ?_⟩
    · rw [CombMap.facePerm, Equiv.Perm.mul_apply, P.contactColour_sigma, P.contactColour_alpha, hx,
        Bool.not_true]
    · exact faceClass_restriction_facePerm S.diagram.toCombMap.dual P.ContactKeep
        P.contactKeep_alpha x

/-- **Step 2: a face holding no object contains every dart of the contact map in its class.** -/
theorem faceOf_eq_of_not_holdsObject (P : OsinLemma94RealizedPolygons S)
    {F : P.contactMap.Face} (hF : ¬ P.HoldsObject F) {x₁ x₂ : P.contactMap.Dart}
    (hx₁ : P.contactMap.faceOf x₁ = F) (hcls : ContactClass P x₁.1 x₂.1) :
    P.contactMap.faceOf x₂ = F := by
  obtain ⟨z, hzf, hzc, hxz⟩ := exists_colour_false P x₂
  obtain ⟨o, ho⟩ := OsinLemma94RealizedPolygons.exists_faceOf_eq_objectFace P z hzc
  have hcls' : ContactClass P x₁.1 z.1 := Relation.EqvGen.trans _ _ _ hcls hxz
  have hex : ∃ z' : P.contactMap.Dart, P.contactMap.faceOf z' = F ∧
      S.diagram.toCombMap.faceOf z'.1 = OsinLemma94RealizedPolygons.objectFace S o := by
    by_contra hno
    refine hF ?_
    unfold OsinLemma94RealizedPolygons.HoldsObject
    exact ⟨x₁, hx₁, z.1, hcls', o, ho, fun z' h1 h2 => hno ⟨z', h1, h2⟩⟩
  obtain ⟨z', hz'F, hz'o⟩ := hex
  have hc1 : P.contactMap.componentOf x₁ z' :=
    componentOf_of_faceOf_eq' P.contactMap (hx₁.trans hz'F.symm)
  have hc2 : P.contactMap.componentOf z' z :=
    componentOf_of_vertexOf_eq' P.contactMap
      (OsinLemma94RealizedPolygons.vertexOf_eq_of_faceOf_eq P (hz'o.trans ho.symm))
  have hface : P.contactMap.faceOf x₁ = P.contactMap.faceOf z :=
    CombMap.PredicateRestriction.faceOf_eq_of_faceClass_of_componentOf
      S.diagram.toCombMap.dual P.ContactKeep P.contactKeep_alpha
      (OsinLemma94RealizedPolygons.dual_planar_diagram S)
      (Relation.EqvGen.trans _ _ _ hc1 hc2) hcls'
  exact hzf.symm.trans (hface.symm.trans hx₁)

end ClassInjective

end GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P01EmptyTwoGon

#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P01EmptyTwoGon.faceOf_eq_of_not_holdsObject
