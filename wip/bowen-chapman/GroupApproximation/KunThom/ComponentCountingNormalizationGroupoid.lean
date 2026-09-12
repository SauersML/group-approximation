import GroupApproximation.Matching.FiniteGroupoidCounting
import Mathlib.GroupTheory.Coset.Card
import Mathlib.Algebra.Group.Subgroup.Ker

/-!
# Finite counting for the relative cluster functor

The endgame of Kun and Thom's proof of Theorem 4.1 (arXiv:2608.06222, §4)
compares the cluster groupoid of `σ(Γ)` with its conjugate through a relative
functor.  That functor is faithful and injective on objects, but it is defined
only on a large set `R` of objects.  This file proves the finite statements
the endgame uses.  Every object statement is phrased for an object map on `R`
that is injective and preserves connectedness, so no subgroupoid construction
is needed.

* `card_orbit_inter_le`, `mul_card_orbit_le_of_clean`: the part of an orbit
  lying in `R` injects into the orbit of the image, so a clean orbit (few
  objects outside `R`) is at most a `1 / (1 - ζ)` multiple of the image orbit.
* `card_orbit_inter_add_le`, `nonempty_hom_of_card_orbit_lt`: two disconnected
  objects whose images are connected force the image orbit to contain both
  source orbits.  An image orbit smaller than `(1 - ζ)` times their sum
  therefore connects the two objects.
* `card_eq_of_injective_of_lt_two_mul`: an injective homomorphism of finite
  groups whose target is less than twice as large is an isomorphism.
* `map_bijective_of_isotropy_lt_two_mul`: on a connected pair of objects, a
  faithful functor is bijective on Hom-sets once the isotropy index is below
  `2`.
-/

namespace GroupApproximation
namespace ComponentCountingNormalization

open CategoryTheory

universe u v u' v'

/-! ### Object orbits -/

/-- The part of an orbit lying in `R` injects into the orbit of the image. -/
theorem card_orbit_inter_le {C : Type u} [Groupoid.{v} C] [Fintype C] [DecidableEq C]
    {D : Type u'} [Groupoid.{v'} D] [Fintype D]
    (R : Finset C) (f : C → D) (hinj : Set.InjOn f (R : Set C))
    (hconn : ∀ X ∈ R, ∀ Y ∈ R, Nonempty (X ⟶ Y) → Nonempty (f X ⟶ f Y))
    {X : C} (hX : X ∈ R) :
    (FiniteGroupoid.orbit X ∩ R).card ≤ (FiniteGroupoid.orbit (f X)).card := by
  apply Finset.card_le_card_of_injOn f
  · intro Y hY
    rw [Finset.mem_coe] at hY ⊢
    obtain ⟨hYo, hYR⟩ := Finset.mem_inter.mp hY
    exact (FiniteGroupoid.mem_orbit _ _).mpr
      (hconn X hX Y hYR ((FiniteGroupoid.mem_orbit X Y).mp hYo))
  · apply Set.InjOn.mono _ hinj
    intro Y hY
    exact Finset.mem_coe.mpr (Finset.mem_inter.mp (Finset.mem_coe.mp hY)).2

/-- Removing the objects outside `R` from a clean orbit loses at most a `ζ`
fraction. -/
theorem mul_card_orbit_le_card_orbit_inter {C : Type u} [Groupoid.{v} C] [Fintype C]
    [DecidableEq C] (R : Finset C) (X : C) {ζ : ℝ}
    (hclean : ((FiniteGroupoid.orbit X \ R).card : ℝ) ≤ ζ * (FiniteGroupoid.orbit X).card) :
    (1 - ζ) * (FiniteGroupoid.orbit X).card ≤ ((FiniteGroupoid.orbit X ∩ R).card : ℝ) := by
  have h := Finset.card_sdiff_add_card_inter (FiniteGroupoid.orbit X) R
  have hcast : ((FiniteGroupoid.orbit X \ R).card : ℝ) +
      ((FiniteGroupoid.orbit X ∩ R).card : ℝ) = (FiniteGroupoid.orbit X).card := by
    exact_mod_cast h
  linarith

/-- **One-sided orbit inequality.**  A clean orbit is at most a `1 / (1 - ζ)`
multiple of the orbit of its image. -/
theorem mul_card_orbit_le_of_clean {C : Type u} [Groupoid.{v} C] [Fintype C] [DecidableEq C]
    {D : Type u'} [Groupoid.{v'} D] [Fintype D]
    (R : Finset C) (f : C → D) (hinj : Set.InjOn f (R : Set C))
    (hconn : ∀ X ∈ R, ∀ Y ∈ R, Nonempty (X ⟶ Y) → Nonempty (f X ⟶ f Y))
    {X : C} (hX : X ∈ R) {ζ : ℝ}
    (hclean : ((FiniteGroupoid.orbit X \ R).card : ℝ) ≤ ζ * (FiniteGroupoid.orbit X).card) :
    (1 - ζ) * (FiniteGroupoid.orbit X).card ≤ ((FiniteGroupoid.orbit (f X)).card : ℝ) := by
  have h₁ := mul_card_orbit_le_card_orbit_inter R X hclean
  have h₂ : ((FiniteGroupoid.orbit X ∩ R).card : ℝ) ≤ (FiniteGroupoid.orbit (f X)).card := by
    exact_mod_cast card_orbit_inter_le R f hinj hconn hX
  linarith

/-- **Splitting bound.**  Two disconnected objects of `R` whose images are
connected leave room for both of their orbits in the image orbit. -/
theorem card_orbit_inter_add_le {C : Type u} [Groupoid.{v} C] [Fintype C] [DecidableEq C]
    {D : Type u'} [Groupoid.{v'} D] [Fintype D]
    (R : Finset C) (f : C → D) (hinj : Set.InjOn f (R : Set C))
    (hconn : ∀ X ∈ R, ∀ Y ∈ R, Nonempty (X ⟶ Y) → Nonempty (f X ⟶ f Y))
    {X X' : C} (hX : X ∈ R) (hX' : X' ∈ R) (hdisc : ¬ Nonempty (X ⟶ X'))
    (himage : Nonempty (f X ⟶ f X')) :
    (FiniteGroupoid.orbit X ∩ R).card + (FiniteGroupoid.orbit X' ∩ R).card ≤
      (FiniteGroupoid.orbit (f X)).card := by
  have hunion : ((FiniteGroupoid.orbit X ∩ R) ∪ (FiniteGroupoid.orbit X' ∩ R)).card =
      (FiniteGroupoid.orbit X ∩ R).card + (FiniteGroupoid.orbit X' ∩ R).card := by
    apply Finset.card_union_eq_card_add_card.mpr
    rw [Finset.disjoint_left]
    intro Y hY hY'
    obtain ⟨g⟩ := (FiniteGroupoid.mem_orbit X Y).mp (Finset.mem_inter.mp hY).1
    obtain ⟨g'⟩ := (FiniteGroupoid.mem_orbit X' Y).mp (Finset.mem_inter.mp hY').1
    exact hdisc ⟨g ≫ inv g'⟩
  rw [← hunion]
  have hmemR : ∀ Y, Y ∈ ((FiniteGroupoid.orbit X ∩ R) ∪ (FiniteGroupoid.orbit X' ∩ R)) →
      Y ∈ R := by
    intro Y hY
    rcases Finset.mem_union.mp hY with h | h
    · exact (Finset.mem_inter.mp h).2
    · exact (Finset.mem_inter.mp h).2
  apply Finset.card_le_card_of_injOn f
  · intro Y hY
    rw [Finset.mem_coe] at hY ⊢
    rcases Finset.mem_union.mp hY with hY | hY
    · obtain ⟨hYo, hYR⟩ := Finset.mem_inter.mp hY
      exact (FiniteGroupoid.mem_orbit _ _).mpr
        (hconn X hX Y hYR ((FiniteGroupoid.mem_orbit X Y).mp hYo))
    · obtain ⟨hYo, hYR⟩ := Finset.mem_inter.mp hY
      obtain ⟨a⟩ := himage
      obtain ⟨b⟩ := hconn X' hX' Y hYR ((FiniteGroupoid.mem_orbit X' Y).mp hYo)
      exact (FiniteGroupoid.mem_orbit _ _).mpr ⟨a ≫ b⟩
  · intro Y hY Z hZ hYZ
    exact hinj (Finset.mem_coe.mpr (hmemR Y (Finset.mem_coe.mp hY)))
      (Finset.mem_coe.mpr (hmemR Z (Finset.mem_coe.mp hZ))) hYZ

/-- **Splitting contradiction.**  If the images of two clean objects of `R` are
connected and the image orbit is smaller than `(1 - ζ)` times the sum of the
two source orbits, the two objects are connected. -/
theorem nonempty_hom_of_card_orbit_lt {C : Type u} [Groupoid.{v} C] [Fintype C]
    [DecidableEq C] {D : Type u'} [Groupoid.{v'} D] [Fintype D]
    (R : Finset C) (f : C → D) (hinj : Set.InjOn f (R : Set C))
    (hconn : ∀ X ∈ R, ∀ Y ∈ R, Nonempty (X ⟶ Y) → Nonempty (f X ⟶ f Y))
    {X X' : C} (hX : X ∈ R) (hX' : X' ∈ R) {ζ : ℝ}
    (hclean : ((FiniteGroupoid.orbit X \ R).card : ℝ) ≤ ζ * (FiniteGroupoid.orbit X).card)
    (hclean' : ((FiniteGroupoid.orbit X' \ R).card : ℝ) ≤ ζ * (FiniteGroupoid.orbit X').card)
    (himage : Nonempty (f X ⟶ f X'))
    (hsmall : ((FiniteGroupoid.orbit (f X)).card : ℝ) <
      (1 - ζ) * ((FiniteGroupoid.orbit X).card + (FiniteGroupoid.orbit X').card)) :
    Nonempty (X ⟶ X') := by
  by_contra hdisc
  have hsplit := card_orbit_inter_add_le R f hinj hconn hX hX' hdisc himage
  have h₁ := mul_card_orbit_le_card_orbit_inter R X hclean
  have h₂ := mul_card_orbit_le_card_orbit_inter R X' hclean'
  have hcast : ((FiniteGroupoid.orbit X ∩ R).card : ℝ) +
      ((FiniteGroupoid.orbit X' ∩ R).card : ℝ) ≤ (FiniteGroupoid.orbit (f X)).card := by
    exact_mod_cast hsplit
  linarith

/-! ### Isotropy -/

/-- An injective homomorphism of finite groups: the source order divides the
target order. -/
theorem card_dvd_of_injective {G H : Type*} [Group G] [Group H] [Fintype G] [Fintype H]
    (φ : G →* H) (hφ : Function.Injective φ) : Fintype.card G ∣ Fintype.card H := by
  have hrange : Nat.card φ.range = Nat.card G :=
    Nat.card_congr (MonoidHom.ofInjective hφ).toEquiv.symm
  have hdvd := Subgroup.card_subgroup_dvd_card φ.range
  rw [hrange, Nat.card_eq_fintype_card, Nat.card_eq_fintype_card] at hdvd
  exact hdvd

/-- **Index below two.**  An injective homomorphism into a finite group less
than twice as large as its source is onto. -/
theorem card_eq_of_injective_of_lt_two_mul {G H : Type*} [Group G] [Group H] [Fintype G]
    [Fintype H] (φ : G →* H) (hφ : Function.Injective φ)
    (hlt : Fintype.card H < 2 * Fintype.card G) :
    Fintype.card H = Fintype.card G := by
  obtain ⟨d, hd⟩ := card_dvd_of_injective φ hφ
  have hH : 0 < Fintype.card H := Fintype.card_pos
  have hd0 : d ≠ 0 := by
    rintro rfl
    rw [mul_zero] at hd
    omega
  have hd2 : d < 2 := by
    by_contra h
    have h2 : 2 ≤ d := not_lt.mp h
    have hmul : Fintype.card G * 2 ≤ Fintype.card G * d := Nat.mul_le_mul le_rfl h2
    linarith
  have hd1 : d = 1 := by omega
  rw [hd, hd1, mul_one]

/-- A functor restricted to one vertex group, as a group homomorphism. -/
def vertexGroupHom {C : Type u} [Groupoid.{v} C] {D : Type u'} [Groupoid.{v'} D]
    (F : C ⥤ D) (X : C) : (X ⟶ X) →* (F.obj X ⟶ F.obj X) where
  toFun := F.map
  map_one' := F.map_id X
  map_mul' f g := F.map_comp f g

/-- **Hom-set bijection.**  On a connected pair of objects a faithful functor
is surjective on the Hom-set once the image isotropy group is less than twice
as large as the source isotropy group. -/
theorem map_surjective_of_isotropy_lt_two_mul {C : Type u} [Groupoid.{v} C]
    {D : Type u'} [Groupoid.{v'} D] (F : C ⥤ D) [F.Faithful] {X Y : C} (f : X ⟶ Y)
    [Fintype (X ⟶ X)] [Fintype (X ⟶ Y)]
    [Fintype (F.obj X ⟶ F.obj X)] [Fintype (F.obj X ⟶ F.obj Y)]
    (hlt : Fintype.card (F.obj X ⟶ F.obj X) < 2 * Fintype.card (X ⟶ X)) :
    Function.Surjective (F.map : (X ⟶ Y) → (F.obj X ⟶ F.obj Y)) := by
  apply FiniteGroupoid.map_surjective_of_faithful_of_vertexGroup_card_eq F f
  exact (card_eq_of_injective_of_lt_two_mul (vertexGroupHom F X) F.map_injective hlt).symm

theorem map_bijective_of_isotropy_lt_two_mul {C : Type u} [Groupoid.{v} C]
    {D : Type u'} [Groupoid.{v'} D] (F : C ⥤ D) [F.Faithful] {X Y : C} (f : X ⟶ Y)
    [Fintype (X ⟶ X)] [Fintype (X ⟶ Y)]
    [Fintype (F.obj X ⟶ F.obj X)] [Fintype (F.obj X ⟶ F.obj Y)]
    (hlt : Fintype.card (F.obj X ⟶ F.obj X) < 2 * Fintype.card (X ⟶ X)) :
    Function.Bijective (F.map : (X ⟶ Y) → (F.obj X ⟶ F.obj Y)) :=
  ⟨F.map_injective, map_surjective_of_isotropy_lt_two_mul F f hlt⟩

end ComponentCountingNormalization
end GroupApproximation
