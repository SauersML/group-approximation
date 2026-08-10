import Mathlib.CategoryTheory.Groupoid.VertexGroup
import Mathlib.CategoryTheory.Functor.FullyFaithful
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.EquivFin

/-!
# Counting in finite groupoids

The permutation-centralizer argument eventually reduces fullness of a
faithful relative functor to two integer equalities: equality of object-orbit
sizes and equality of isotropy-group orders.  This file proves the underlying
finite groupoid facts directly from Mathlib's `Groupoid` interface.
-/

namespace NonsoficGroupsExist
namespace FiniteGroupoid

open CategoryTheory

universe u v

variable {C : Type u} [Groupoid.{v} C]

/-- Right composition by one groupoid arrow identifies the source isotropy
group with the entire Hom-set to its target. -/
noncomputable def vertexHomEquiv {X Y : C} (f : X ⟶ Y) :
    (X ⟶ X) ≃ (X ⟶ Y) where
  toFun a := a ≫ f
  invFun b := b ≫ inv f
  left_inv a := by simp
  right_inv b := by simp

/-- Every nonempty Hom-set is a torsor for the source isotropy group. -/
theorem card_hom_eq_card_vertexGroup {X Y : C} [Fintype (X ⟶ X)]
    [Fintype (X ⟶ Y)] (f : X ⟶ Y) :
    Fintype.card (X ⟶ Y) = Fintype.card (X ⟶ X) := by
  exact Fintype.card_congr (vertexHomEquiv f).symm

/-- The object orbit of `X`, represented as a finite set. -/
noncomputable def orbit [Fintype C] (X : C) : Finset C :=
  by
    classical
    exact Finset.univ.filter fun Y ↦ Nonempty (X ⟶ Y)

@[simp] theorem mem_orbit [Fintype C] (X Y : C) :
    Y ∈ orbit X ↔ Nonempty (X ⟶ Y) := by
  simp [orbit]

theorem self_mem_orbit [Fintype C] (X : C) : X ∈ orbit X := by
  exact (mem_orbit X X).2 ⟨𝟙 X⟩

/-- Objects joined by an arrow have the same finite orbit. -/
theorem orbit_eq_of_hom [Fintype C] {X Y : C} (f : X ⟶ Y) :
    orbit X = orbit Y := by
  ext Z
  simp only [mem_orbit]
  constructor
  · rintro ⟨g⟩
    exact ⟨inv f ≫ g⟩
  · rintro ⟨g⟩
    exact ⟨f ≫ g⟩

/-- Conjugation along an arrow identifies the two finite isotropy groups. -/
theorem card_vertexGroup_eq_of_hom {X Y : C} [Fintype (X ⟶ X)]
    [Fintype (Y ⟶ Y)] (f : X ⟶ Y) :
    Fintype.card (X ⟶ X) = Fintype.card (Y ⟶ Y) := by
  exact Fintype.card_congr (CategoryTheory.Groupoid.vertexGroupIsomOfMap f).toEquiv

variable {D : Type*} [Groupoid D]

/-- A faithful functor injects each finite Hom-set. -/
theorem card_hom_le_of_faithful (F : C ⥤ D) [F.Faithful]
    (X Y : C) [Fintype (X ⟶ Y)] [Fintype (F.obj X ⟶ F.obj Y)] :
    Fintype.card (X ⟶ Y) ≤ Fintype.card (F.obj X ⟶ F.obj Y) :=
  Fintype.card_le_of_injective F.map F.map_injective

/-- For finite Hom-sets, a faithful map is surjective as soon as their
cardinalities agree.  This is the finite co-Hopfian step used to upgrade a
relative cluster functor from faithful to full. -/
theorem map_surjective_of_faithful_of_card_eq
    (F : C ⥤ D) [F.Faithful] (X Y : C)
    [Fintype (X ⟶ Y)] [Fintype (F.obj X ⟶ F.obj Y)]
    (hcard : Fintype.card (X ⟶ Y) =
      Fintype.card (F.obj X ⟶ F.obj Y)) :
    Function.Surjective
      (F.map : (X ⟶ Y) → (F.obj X ⟶ F.obj Y)) := by
  exact ((Fintype.bijective_iff_injective_and_card _).2
    ⟨F.map_injective, hcard⟩).surjective

/-- On a connected pair of objects, equality of source isotropy orders is
already enough to make a faithful functor surjective on that Hom-set. -/
theorem map_surjective_of_faithful_of_vertexGroup_card_eq
    (F : C ⥤ D) [F.Faithful] {X Y : C} (f : X ⟶ Y)
    [Fintype (X ⟶ X)] [Fintype (X ⟶ Y)]
    [Fintype (F.obj X ⟶ F.obj X)] [Fintype (F.obj X ⟶ F.obj Y)]
    (hcard : Fintype.card (X ⟶ X) =
      Fintype.card (F.obj X ⟶ F.obj X)) :
    Function.Surjective
      (F.map : (X ⟶ Y) → (F.obj X ⟶ F.obj Y)) := by
  apply map_surjective_of_faithful_of_card_eq F X Y
  calc
    Fintype.card (X ⟶ Y) = Fintype.card (X ⟶ X) :=
      card_hom_eq_card_vertexGroup f
    _ = Fintype.card (F.obj X ⟶ F.obj X) := hcard
    _ = Fintype.card (F.obj X ⟶ F.obj Y) :=
      (card_hom_eq_card_vertexGroup (F.map f)).symm

end FiniteGroupoid
end NonsoficGroupsExist
