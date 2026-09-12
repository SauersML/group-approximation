import GroupApproximation.KunThom.ComponentCountingRelativeFunctorPresentation
import GroupApproximation.KunThom.CountingEndgameLift
import GroupApproximation.KunThom.CountingEndgameWeights

/-!
# The counting endgame on restricted presentations

The relative cluster functor of a compressor
(`GroupoidPresentation.ClusterMetric.relativeFunctor`) runs between restricted
presentations, `(P.restrict R).Obj ⥤ (Q.restrict D).Obj`.  The finite endgame
`CountingEndgame.exists_bisection_lift` needs the source carried into the
ambient cluster groupoid.  Its hypotheses are counts in the restricted
groupoids, while cleanliness and the concentration (4) of Kun and Thom
(arXiv:2608.06222v3, §4) concern the ambient groupoids.  This file supplies the
bridge.

* `GroupoidPresentation.restrictInclusion`, `restrictInclusionFunctor`: the
  inclusion of a restricted presentation.  It is faithful, full and injective on
  objects, and finite representatives restrict (`restrictRepFinite`).
* `CountingEndgame.card_orbit_image_inter_le`: for a full functor, the part of
  the orbit of an image lying in the image has at most as many objects as the
  orbit.
* `CountingEndgame.card_orbit_le_card_orbit_map`: a functor injective on objects
  does not shrink orbits.
* `CountingEndgame.card_vertexGroup_map_eq`: a full and faithful functor
  preserves isotropy orders.
* `CountingEndgame.mul_card_orbit_le_card_orbit_map_of_clean` and
  `card_vertexGroup_le_card_vertexGroup_map`: the one-sided inequalities (2) and
  (3) of Kun and Thom, with ambient orbits and isotropy groups.
* `CountingEndgame.card_orbit_lt_add_of_clean` and
  `card_vertexGroup_lt_two_mul_of_ratio`: the two count hypotheses of
  `exists_bisection_lift`, from ambient cleanliness and ratio bounds.
-/

universe u v u' v' u'' v''

namespace GroupApproximation
namespace GroupoidPresentation

open CategoryTheory

variable {I : Type u}

/-- The inclusion of a restricted presentation into the ambient presentation. -/
def restrictInclusion (P : GroupoidPresentation.{u, v} I) (R : Set I) :
    (P.restrict R).Morphism P where
  obj X := X.1
  map f := f
  map_respects h := h
  map_one X := (P.rel X.1 X.1).refl' _
  map_comp _ _ := (P.rel _ _).refl' _

/-- The inclusion functor of a restricted presentation. -/
def restrictInclusionFunctor (P : GroupoidPresentation.{u, v} I) (R : Set I) :
    (P.restrict R).Obj ⥤ P.Obj :=
  (P.restrictInclusion R).toFunctor

theorem restrictInclusionFunctor_obj_val (P : GroupoidPresentation.{u, v} I) (R : Set I)
    (X : (P.restrict R).Obj) : ((P.restrictInclusionFunctor R).obj X).val = X.val.1 :=
  rfl

theorem restrictInclusionFunctor_obj_injective (P : GroupoidPresentation.{u, v} I)
    (R : Set I) : Function.Injective (P.restrictInclusionFunctor R).obj := by
  intro X Y h
  obtain ⟨x⟩ := X
  obtain ⟨y⟩ := Y
  have h₁ : x.1 = y.1 := congrArg Obj.val h
  have h₂ : x = y := Subtype.ext h₁
  subst h₂
  rfl

instance restrictInclusionFunctor_faithful (P : GroupoidPresentation.{u, v} I) (R : Set I) :
    (P.restrictInclusionFunctor R).Faithful :=
  (P.restrictInclusion R).toFunctor_faithful fun h ↦ h

instance restrictInclusionFunctor_full (P : GroupoidPresentation.{u, v} I) (R : Set I) :
    (P.restrictInclusionFunctor R).Full where
  map_surjective {X Y} f := by
    induction f using Quotient.inductionOn with
    | _ f => exact ⟨(P.restrict R).ofRep (X := X) (Y := Y) f, rfl⟩

/-- Finite representatives restrict. -/
instance restrictRepFinite (P : GroupoidPresentation.{u, v} I) (R : Set I)
    [∀ i j, Finite (P.Rep i j)] (X Y : R) : Finite ((P.restrict R).Rep X Y) :=
  inferInstanceAs (Finite (P.Rep X.1 Y.1))

end GroupoidPresentation

namespace CountingEndgame

open CategoryTheory

/-- For a full functor `J`, the part of the orbit of `J X` lying in the image of
`J` has at most as many objects as the orbit of `X`. -/
theorem card_orbit_image_inter_le {C : Type u} [Groupoid.{v} C] [Fintype C]
    {D : Type u'} [Groupoid.{v'} D] [Fintype D] [DecidableEq D] (J : C ⥤ D) [J.Full]
    (X : C) :
    (FiniteGroupoid.orbit (J.obj X) ∩ Finset.univ.image J.obj).card ≤
      (FiniteGroupoid.orbit X).card := by
  have hsub : FiniteGroupoid.orbit (J.obj X) ∩ Finset.univ.image J.obj ⊆
      (FiniteGroupoid.orbit X).image J.obj := by
    intro Z hZ
    obtain ⟨hZo, hZim⟩ := Finset.mem_inter.mp hZ
    obtain ⟨Y, _, hYZ⟩ := Finset.mem_image.mp hZim
    rw [← hYZ] at hZo ⊢
    obtain ⟨f⟩ := (FiniteGroupoid.mem_orbit (J.obj X) (J.obj Y)).mp hZo
    exact Finset.mem_image_of_mem J.obj ((FiniteGroupoid.mem_orbit X Y).mpr ⟨J.preimage f⟩)
  exact (Finset.card_le_card hsub).trans Finset.card_image_le

/-- A functor injective on objects does not shrink orbits. -/
theorem card_orbit_le_card_orbit_map {C : Type u} [Groupoid.{v} C] [Fintype C]
    [DecidableEq C] {D : Type u'} [Groupoid.{v'} D] [Fintype D] (F : C ⥤ D)
    (hobj : Function.Injective F.obj) (X : C) :
    (FiniteGroupoid.orbit X).card ≤ (FiniteGroupoid.orbit (F.obj X)).card := by
  have h := ComponentCountingNormalization.card_orbit_inter_le Finset.univ F.obj
    (fun _ _ _ _ hYZ ↦ hobj hYZ) (fun _ _ _ _ hYZ ↦ Nonempty.map (fun g ↦ F.map g) hYZ)
    (Finset.mem_univ X)
  simpa only [Finset.inter_univ] using h

/-- A full and faithful functor preserves isotropy orders. -/
theorem card_vertexGroup_map_eq {C : Type u} [Groupoid.{v} C] {D : Type u'}
    [Groupoid.{v'} D] (J : C ⥤ D) [J.Full] [J.Faithful] (X : C) [Fintype (X ⟶ X)]
    [Fintype (J.obj X ⟶ J.obj X)] :
    Fintype.card (J.obj X ⟶ J.obj X) = Fintype.card (X ⟶ X) :=
  (Fintype.card_congr (Equiv.ofBijective (J.map (X := X) (Y := X))
    ⟨J.map_injective, J.map_surjective⟩)).symm

/-- **One-sided orbit inequality (2).**  Let `J : C' ⥤ C` be full and
`F : C' ⥤ D` injective on objects.  If the ambient orbit of `J X` loses at most a
`ζ` fraction of its objects outside the image of `J`, then `1 - ζ` times that
ambient orbit is at most the orbit of `F X`. -/
theorem mul_card_orbit_le_card_orbit_map_of_clean {C' : Type u} [Groupoid.{v} C']
    [Fintype C'] [DecidableEq C'] {C : Type u'} [Groupoid.{v'} C] [Fintype C]
    [DecidableEq C] {D : Type u''} [Groupoid.{v''} D] [Fintype D] (J : C' ⥤ C) [J.Full]
    (F : C' ⥤ D) (hF : Function.Injective F.obj) (X : C') {ζ : ℝ}
    (hclean : ((FiniteGroupoid.orbit (J.obj X) \ Finset.univ.image J.obj).card : ℝ) ≤
      ζ * (FiniteGroupoid.orbit (J.obj X)).card) :
    (1 - ζ) * ((FiniteGroupoid.orbit (J.obj X)).card : ℝ) ≤
      (FiniteGroupoid.orbit (F.obj X)).card := by
  have h₁ := ComponentCountingNormalization.mul_card_orbit_le_card_orbit_inter
    (Finset.univ.image J.obj) (J.obj X) hclean
  have h₂ : ((FiniteGroupoid.orbit (J.obj X) ∩ Finset.univ.image J.obj).card : ℝ) ≤
      (FiniteGroupoid.orbit X).card := by
    exact_mod_cast card_orbit_image_inter_le J X
  have h₃ : ((FiniteGroupoid.orbit X).card : ℝ) ≤ (FiniteGroupoid.orbit (F.obj X)).card := by
    exact_mod_cast card_orbit_le_card_orbit_map F hF X
  linarith

/-- **One-sided isotropy inequality (3).**  If `J : C' ⥤ C` is full and faithful
and `F : C' ⥤ D` is faithful, the ambient isotropy order of `J X` is at most the
isotropy order of `F X`. -/
theorem card_vertexGroup_le_card_vertexGroup_map {C' : Type u} [Groupoid.{v} C']
    {C : Type u'} [Groupoid.{v'} C] {D : Type u''} [Groupoid.{v''} D] (J : C' ⥤ C)
    [J.Full] [J.Faithful] (F : C' ⥤ D) [F.Faithful] (X : C') [Fintype (X ⟶ X)]
    [Fintype (J.obj X ⟶ J.obj X)] [Fintype (F.obj X ⟶ F.obj X)] :
    Fintype.card (J.obj X ⟶ J.obj X) ≤ Fintype.card (F.obj X ⟶ F.obj X) := by
  rw [card_vertexGroup_map_eq J X]
  exact FiniteGroupoid.card_hom_le_of_faithful F X X

/-- **The orbit count of `exists_bisection_lift` from ambient data.**  Let
`J : C' ⥤ C` be full.  If the ambient orbits of `J X` and `J X'` lose at most a
`ζ` fraction of their objects outside the image of `J`, and each is at least a
`1 / ρ` fraction of the orbit of `F X`, with `ρ < 2 (1 - ζ)`, then the orbit of
`F X` has fewer objects than the orbits of `X` and `X'` together. -/
theorem card_orbit_lt_add_of_clean {C' : Type u} [Groupoid.{v} C'] [Fintype C']
    {C : Type u'} [Groupoid.{v'} C] [Fintype C] [DecidableEq C] {D : Type u''}
    [Groupoid.{v''} D] [Fintype D] (J : C' ⥤ C) [J.Full] (F : C' ⥤ D) {X X' : C'}
    {ζ ρ : ℝ} (hρ : 0 < ρ) (hζρ : ρ < 2 * (1 - ζ))
    (hclean : ((FiniteGroupoid.orbit (J.obj X) \ Finset.univ.image J.obj).card : ℝ) ≤
      ζ * (FiniteGroupoid.orbit (J.obj X)).card)
    (hclean' : ((FiniteGroupoid.orbit (J.obj X') \ Finset.univ.image J.obj).card : ℝ) ≤
      ζ * (FiniteGroupoid.orbit (J.obj X')).card)
    (hratio : ((FiniteGroupoid.orbit (F.obj X)).card : ℝ) ≤
      ρ * (FiniteGroupoid.orbit (J.obj X)).card)
    (hratio' : ((FiniteGroupoid.orbit (F.obj X)).card : ℝ) ≤
      ρ * (FiniteGroupoid.orbit (J.obj X')).card) :
    (FiniteGroupoid.orbit (F.obj X)).card <
      (FiniteGroupoid.orbit X).card + (FiniteGroupoid.orbit X').card := by
  have h₁ := ComponentCountingNormalization.mul_card_orbit_le_card_orbit_inter
    (Finset.univ.image J.obj) (J.obj X) hclean
  have h₁' := ComponentCountingNormalization.mul_card_orbit_le_card_orbit_inter
    (Finset.univ.image J.obj) (J.obj X') hclean'
  have h₂ : ((FiniteGroupoid.orbit (J.obj X) ∩ Finset.univ.image J.obj).card : ℝ) ≤
      (FiniteGroupoid.orbit X).card := by
    exact_mod_cast card_orbit_image_inter_le J X
  have h₂' : ((FiniteGroupoid.orbit (J.obj X') ∩ Finset.univ.image J.obj).card : ℝ) ≤
      (FiniteGroupoid.orbit X').card := by
    exact_mod_cast card_orbit_image_inter_le J X'
  exact card_lt_add_of_ratio hρ hζρ
    (Finset.card_pos.mpr ⟨F.obj X, FiniteGroupoid.self_mem_orbit (F.obj X)⟩)
    (h₁.trans h₂) (h₁'.trans h₂') hratio hratio'

/-- **The isotropy index of `exists_bisection_lift` from ambient data.**  If
`J : C' ⥤ C` is full and faithful and the isotropy order of `F X` is at most
`ρ < 2` times the ambient isotropy order of `J X`, the isotropy index of `F` at
`X` is below `2`. -/
theorem card_vertexGroup_lt_two_mul_of_ratio {C' : Type u} [Groupoid.{v} C']
    {C : Type u'} [Groupoid.{v'} C] {D : Type u''} [Groupoid.{v''} D] (J : C' ⥤ C)
    [J.Full] [J.Faithful] (F : C' ⥤ D) (X : C') [Fintype (X ⟶ X)]
    [Fintype (J.obj X ⟶ J.obj X)] [Fintype (F.obj X ⟶ F.obj X)] {ρ : ℝ} (hρ : ρ < 2)
    (hratio : (Fintype.card (F.obj X ⟶ F.obj X) : ℝ) ≤
      ρ * Fintype.card (J.obj X ⟶ J.obj X)) :
    Fintype.card (F.obj X ⟶ F.obj X) < 2 * Fintype.card (X ⟶ X) := by
  rw [card_vertexGroup_map_eq J X] at hratio
  exact lt_two_mul_of_ratio hρ (Fintype.card_pos_iff.mpr ⟨𝟙 X⟩) hratio

end CountingEndgame
end GroupApproximation
