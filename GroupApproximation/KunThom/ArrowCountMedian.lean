import GroupApproximation.KunThom.CountingEndgameLift

/-!
# One median for orbit sizes and isotropy orders

Kun and Thom's proof of Theorem 4.1 (arXiv:2608.06222v3, §4) amplifies two
one-sided inequalities into ratios tending to `1`, one for the orbit sizes and
one for the isotropy orders of the cluster groupoid.  A single application of
the median lemma to their product suffices.

For an object `X` of a finite groupoid, `arrowCount X` is the number of arrows
out of `X`, its orbit size times its isotropy order.

* `mul_arrowCount_le_of_clean`: a clean orbit inequality and an isotropy
  inequality give the one-sided drift `(1 - ζ) · arrowCount X ≤ arrowCount (f X)`,
  in the form consumed by `MedianVertexForm.localRatio_negligible`.
* Suppose `arrowCount (f X) ≤ (1 + η) · arrowCount X` with `0 ≤ η` and `η + 2ζ < 1`.
  - `card_vertexGroup_lt_two_mul_of_arrowCount`: the isotropy index at `X` is
    below `2`.
  - `card_orbit_lt_of_arrowCount`: for a connected image pair, the image orbit is
    smaller than `(1 - ζ)` times the two source orbits.
  - `nonempty_hom_of_arrowCount`: composes the two with
    `ComponentCountingNormalization.nonempty_hom_of_card_orbit_lt`.
* `map_bijective_of_arrowCount`: the same conclusion for a faithful functor
  injective on objects.  It supplies both hypotheses of
  `CountingEndgame.map_bijective_of_counts` from the two arrow-count ratios.

The only arithmetic is in the first section.  An orbit that drops by at most
the factor `1 - ζ`, together with a product that rises by at most the factor
`1 + η`, bounds the rise of the isotropy order by `(1 + η) / (1 - ζ) < 2`.
-/

namespace GroupApproximation
namespace ArrowCountMedian

open CategoryTheory

universe u v u' v'

/-! ### Real arithmetic -/

/-- An orbit inequality and an isotropy inequality multiply. -/
theorem mul_le_mul_of_orbit_isotropy {o a k k' ζ : ℝ} (ha : 0 ≤ a) (hk : 0 ≤ k)
    (horbit : (1 - ζ) * o ≤ a) (hvert : k ≤ k') :
    (1 - ζ) * (o * k) ≤ a * k' := by
  have h₁ : (1 - ζ) * o * k ≤ a * k := mul_le_mul_of_nonneg_right horbit hk
  have h₂ : a * k ≤ a * k' := mul_le_mul_of_nonneg_left hvert ha
  linarith

/-- **Isotropy index below two.**  If the orbit drops by at most the factor
`1 - ζ` and the product rises by at most the factor `1 + η`, with `η + 2ζ < 1`,
the isotropy order less than doubles. -/
theorem arrowRatio_isotropy_lt_two_mul {o a k k' ζ η : ℝ} (ho : 0 < o) (hk : 0 < k)
    (hk' : 0 ≤ k') (hη : 0 ≤ η) (hηζ : η + 2 * ζ < 1)
    (horbit : (1 - ζ) * o ≤ a) (hratio : a * k' ≤ (1 + η) * (o * k)) :
    k' < 2 * k := by
  by_contra hcon
  have hge : 2 * k ≤ k' := not_lt.mp hcon
  have hζo : 0 ≤ (1 - ζ) * o := mul_nonneg (by linarith) ho.le
  have h₁ : (1 - ζ) * o * k' ≤ a * k' := mul_le_mul_of_nonneg_right horbit hk'
  have h₂ : (1 - ζ) * o * (2 * k) ≤ (1 - ζ) * o * k' := mul_le_mul_of_nonneg_left hge hζo
  have hpos : 0 < (1 - η - 2 * ζ) * (o * k) := mul_pos (by linarith) (mul_pos ho hk)
  linarith

/-- **Orbit ratio.**  If the isotropy order does not drop, the orbit rises by at
most the factor `1 + η`. -/
theorem arrowRatio_orbit_le {o a k k' η : ℝ} (ha : 0 ≤ a) (hk : 0 < k) (hvert : k ≤ k')
    (hratio : a * k' ≤ (1 + η) * (o * k)) :
    a ≤ (1 + η) * o := by
  by_contra hcon
  have hlt : (1 + η) * o < a := not_le.mp hcon
  have h₁ : a * k ≤ a * k' := mul_le_mul_of_nonneg_left hvert ha
  have hpos : 0 < (a - (1 + η) * o) * k := mul_pos (by linarith) hk
  linarith

/-- **Splitting bound.**  Two positive orbits that each bound the common image
orbit up to the factor `1 + η` exceed it together by more than the factor
`1 / (1 - ζ)`, once `η + 2ζ < 1`. -/
theorem arrowRatio_orbit_lt_add {o o' a ζ η : ℝ} (ho : 0 < o) (ho' : 0 < o')
    (hηζ : η + 2 * ζ < 1) (h : a ≤ (1 + η) * o) (h' : a ≤ (1 + η) * o') :
    a < (1 - ζ) * (o + o') := by
  have hpos : 0 < (1 - η - 2 * ζ) * (o + o') := mul_pos (by linarith) (by linarith)
  linarith

/-! ### Arrow counts -/

/-- The number of arrows out of `X`: its orbit size times its isotropy order. -/
noncomputable def arrowCount {C : Type u} [Groupoid.{v} C] [Fintype C] (X : C)
    [Fintype (X ⟶ X)] : ℕ :=
  (FiniteGroupoid.orbit X).card * Fintype.card (X ⟶ X)

/-- Every object has at least one arrow, its identity. -/
theorem one_le_arrowCount {C : Type u} [Groupoid.{v} C] [Fintype C] (X : C)
    [Fintype (X ⟶ X)] : 1 ≤ arrowCount X := by
  unfold arrowCount
  exact mul_pos (Finset.card_pos.mpr ⟨X, FiniteGroupoid.self_mem_orbit X⟩)
    (Fintype.card_pos_iff.mpr ⟨𝟙 X⟩)

/-- The arrow count as a product of real numbers. -/
theorem arrowCount_cast {C : Type u} [Groupoid.{v} C] [Fintype C] (X : C)
    [Fintype (X ⟶ X)] :
    (arrowCount X : ℝ) = ((FiniteGroupoid.orbit X).card : ℝ) * Fintype.card (X ⟶ X) := by
  unfold arrowCount
  exact Nat.cast_mul _ _

theorem card_orbit_pos {C : Type u} [Groupoid.{v} C] [Fintype C] (X : C) :
    (0 : ℝ) < (FiniteGroupoid.orbit X).card := by
  have h : 0 < (FiniteGroupoid.orbit X).card :=
    Finset.card_pos.mpr ⟨X, FiniteGroupoid.self_mem_orbit X⟩
  exact_mod_cast h

theorem card_vertexGroup_pos {C : Type u} [Groupoid.{v} C] (X : C) [Fintype (X ⟶ X)] :
    (0 : ℝ) < Fintype.card (X ⟶ X) := by
  have h : 0 < Fintype.card (X ⟶ X) := Fintype.card_pos_iff.mpr ⟨𝟙 X⟩
  exact_mod_cast h

/-- **One-sided drift of the arrow count.**  A clean orbit of `R` and an isotropy
inequality give `(1 - ζ) · arrowCount X ≤ arrowCount (f X)`. -/
theorem mul_arrowCount_le_of_clean {C : Type u} [Groupoid.{v} C] [Fintype C] [DecidableEq C]
    {D : Type u'} [Groupoid.{v'} D] [Fintype D]
    (R : Finset C) (f : C → D) (hinj : Set.InjOn f (R : Set C))
    (hconn : ∀ X ∈ R, ∀ Y ∈ R, Nonempty (X ⟶ Y) → Nonempty (f X ⟶ f Y))
    {X : C} (hX : X ∈ R) [Fintype (X ⟶ X)] [Fintype (f X ⟶ f X)] {ζ : ℝ}
    (hclean : ((FiniteGroupoid.orbit X \ R).card : ℝ) ≤ ζ * (FiniteGroupoid.orbit X).card)
    (hvert : Fintype.card (X ⟶ X) ≤ Fintype.card (f X ⟶ f X)) :
    (1 - ζ) * (arrowCount X : ℝ) ≤ arrowCount (f X) := by
  have horbit :=
    ComponentCountingNormalization.mul_card_orbit_le_of_clean R f hinj hconn hX hclean
  have hvert' : (Fintype.card (X ⟶ X) : ℝ) ≤ Fintype.card (f X ⟶ f X) := by
    exact_mod_cast hvert
  rw [arrowCount_cast, arrowCount_cast]
  exact mul_le_mul_of_orbit_isotropy (Nat.cast_nonneg _) (Nat.cast_nonneg _) horbit hvert'

/-- **Isotropy index below two from one arrow-count ratio.** -/
theorem card_vertexGroup_lt_two_mul_of_arrowCount {C : Type u} [Groupoid.{v} C] [Fintype C]
    [DecidableEq C] {D : Type u'} [Groupoid.{v'} D] [Fintype D]
    (R : Finset C) (f : C → D) (hinj : Set.InjOn f (R : Set C))
    (hconn : ∀ X ∈ R, ∀ Y ∈ R, Nonempty (X ⟶ Y) → Nonempty (f X ⟶ f Y))
    {X : C} (hX : X ∈ R) [Fintype (X ⟶ X)] [Fintype (f X ⟶ f X)] {ζ η : ℝ}
    (hη : 0 ≤ η) (hηζ : η + 2 * ζ < 1)
    (hclean : ((FiniteGroupoid.orbit X \ R).card : ℝ) ≤ ζ * (FiniteGroupoid.orbit X).card)
    (hratio : (arrowCount (f X) : ℝ) ≤ (1 + η) * arrowCount X) :
    Fintype.card (f X ⟶ f X) < 2 * Fintype.card (X ⟶ X) := by
  have horbit :=
    ComponentCountingNormalization.mul_card_orbit_le_of_clean R f hinj hconn hX hclean
  rw [arrowCount_cast, arrowCount_cast] at hratio
  have h := arrowRatio_isotropy_lt_two_mul (card_orbit_pos X) (card_vertexGroup_pos X)
    (Nat.cast_nonneg _) hη hηζ horbit hratio
  exact_mod_cast h

/-- **Orbit ratio from one arrow-count ratio.**  If the isotropy order does not
drop, the image orbit is at most `1 + η` times the source orbit. -/
theorem card_orbit_le_of_arrowCount {C : Type u} [Groupoid.{v} C] [Fintype C]
    {D : Type u'} [Groupoid.{v'} D] [Fintype D] (f : C → D) {X : C}
    [Fintype (X ⟶ X)] [Fintype (f X ⟶ f X)] {η : ℝ}
    (hvert : Fintype.card (X ⟶ X) ≤ Fintype.card (f X ⟶ f X))
    (hratio : (arrowCount (f X) : ℝ) ≤ (1 + η) * arrowCount X) :
    ((FiniteGroupoid.orbit (f X)).card : ℝ) ≤ (1 + η) * (FiniteGroupoid.orbit X).card := by
  have hvert' : (Fintype.card (X ⟶ X) : ℝ) ≤ Fintype.card (f X ⟶ f X) := by
    exact_mod_cast hvert
  rw [arrowCount_cast, arrowCount_cast] at hratio
  exact arrowRatio_orbit_le (Nat.cast_nonneg _) (card_vertexGroup_pos X) hvert' hratio

/-- **Splitting bound from two arrow-count ratios.**  For a connected image pair,
the image orbit is smaller than `(1 - ζ)` times the two source orbits.  This is
the hypothesis `hsmall` of
`ComponentCountingNormalization.nonempty_hom_of_card_orbit_lt`. -/
theorem card_orbit_lt_of_arrowCount {C : Type u} [Groupoid.{v} C] [Fintype C]
    {D : Type u'} [Groupoid.{v'} D] [Fintype D] (f : C → D) {X X' : C}
    [Fintype (X ⟶ X)] [Fintype (f X ⟶ f X)] [Fintype (X' ⟶ X')] [Fintype (f X' ⟶ f X')]
    {ζ η : ℝ} (hηζ : η + 2 * ζ < 1) (himage : Nonempty (f X ⟶ f X'))
    (hvert : Fintype.card (X ⟶ X) ≤ Fintype.card (f X ⟶ f X))
    (hvert' : Fintype.card (X' ⟶ X') ≤ Fintype.card (f X' ⟶ f X'))
    (hratio : (arrowCount (f X) : ℝ) ≤ (1 + η) * arrowCount X)
    (hratio' : (arrowCount (f X') : ℝ) ≤ (1 + η) * arrowCount X') :
    ((FiniteGroupoid.orbit (f X)).card : ℝ) <
      (1 - ζ) * ((FiniteGroupoid.orbit X).card + (FiniteGroupoid.orbit X').card) := by
  obtain ⟨g⟩ := himage
  have heq : FiniteGroupoid.orbit (f X) = FiniteGroupoid.orbit (f X') :=
    FiniteGroupoid.orbit_eq_of_hom g
  have h := card_orbit_le_of_arrowCount f hvert hratio
  have h' := card_orbit_le_of_arrowCount f hvert' hratio'
  rw [← heq] at h'
  exact arrowRatio_orbit_lt_add (card_orbit_pos X) (card_orbit_pos X') hηζ h h'

/-- **Connectedness from arrow-count ratios.**  Two clean objects of `R` with
connected images and arrow-count ratios at most `1 + η` are connected. -/
theorem nonempty_hom_of_arrowCount {C : Type u} [Groupoid.{v} C] [Fintype C] [DecidableEq C]
    {D : Type u'} [Groupoid.{v'} D] [Fintype D]
    (R : Finset C) (f : C → D) (hinj : Set.InjOn f (R : Set C))
    (hconn : ∀ X ∈ R, ∀ Y ∈ R, Nonempty (X ⟶ Y) → Nonempty (f X ⟶ f Y))
    {X X' : C} (hX : X ∈ R) (hX' : X' ∈ R)
    [Fintype (X ⟶ X)] [Fintype (f X ⟶ f X)] [Fintype (X' ⟶ X')] [Fintype (f X' ⟶ f X')]
    {ζ η : ℝ} (hηζ : η + 2 * ζ < 1)
    (hclean : ((FiniteGroupoid.orbit X \ R).card : ℝ) ≤ ζ * (FiniteGroupoid.orbit X).card)
    (hclean' : ((FiniteGroupoid.orbit X' \ R).card : ℝ) ≤ ζ * (FiniteGroupoid.orbit X').card)
    (himage : Nonempty (f X ⟶ f X'))
    (hvert : Fintype.card (X ⟶ X) ≤ Fintype.card (f X ⟶ f X))
    (hvert' : Fintype.card (X' ⟶ X') ≤ Fintype.card (f X' ⟶ f X'))
    (hratio : (arrowCount (f X) : ℝ) ≤ (1 + η) * arrowCount X)
    (hratio' : (arrowCount (f X') : ℝ) ≤ (1 + η) * arrowCount X') :
    Nonempty (X ⟶ X') :=
  ComponentCountingNormalization.nonempty_hom_of_card_orbit_lt R f hinj hconn hX hX'
    hclean hclean' himage
    (card_orbit_lt_of_arrowCount f hηζ himage hvert hvert' hratio hratio')

/-! ### Functors injective on objects -/

/-- **Isotropy index below two for a functor injective on objects.** -/
theorem card_vertexGroup_lt_two_mul_of_injective {C : Type u} [Groupoid.{v} C] [Fintype C]
    [DecidableEq C] {D : Type u'} [Groupoid.{v'} D] [Fintype D] (F : C ⥤ D)
    (hobj : Function.Injective F.obj) {X : C}
    [Fintype (X ⟶ X)] [Fintype (F.obj X ⟶ F.obj X)] {η : ℝ} (hη : 0 ≤ η) (hη₁ : η < 1)
    (hratio : (arrowCount (F.obj X) : ℝ) ≤ (1 + η) * arrowCount X) :
    Fintype.card (F.obj X ⟶ F.obj X) < 2 * Fintype.card (X ⟶ X) := by
  have hinter := ComponentCountingNormalization.card_orbit_inter_le Finset.univ F.obj
    (fun _ _ _ _ hYZ ↦ hobj hYZ) (fun _ _ _ _ hYZ ↦ Nonempty.map (fun g ↦ F.map g) hYZ)
    (Finset.mem_univ X)
  simp only [Finset.inter_univ] at hinter
  have hle : ((FiniteGroupoid.orbit X).card : ℝ) ≤ (FiniteGroupoid.orbit (F.obj X)).card := by
    exact_mod_cast hinter
  have horbit : (1 - 0) * ((FiniteGroupoid.orbit X).card : ℝ) ≤
      (FiniteGroupoid.orbit (F.obj X)).card := by
    linarith
  rw [arrowCount_cast, arrowCount_cast] at hratio
  have h := arrowRatio_isotropy_lt_two_mul (card_orbit_pos X) (card_vertexGroup_pos X)
    (Nat.cast_nonneg _) hη (by linarith) horbit hratio
  exact_mod_cast h

/-- **Hom-set bijection from arrow-count ratios.**  Let `F` be faithful and
injective on objects, and let the images of `X` and `X'` be connected.  If the
arrow counts of `X` and `X'` rise under `F` by at most the factor `1 + η < 2`,
then `F` is bijective from `X ⟶ X'` onto the image Hom-set. -/
theorem map_bijective_of_arrowCount {C : Type u} [Groupoid.{v} C] [Fintype C]
    [DecidableEq C] {D : Type u'} [Groupoid.{v'} D] [Fintype D] (F : C ⥤ D)
    [F.Faithful] (hobj : Function.Injective F.obj) {X X' : C}
    [Fintype (X ⟶ X)] [Fintype (X ⟶ X')] [Fintype (F.obj X ⟶ F.obj X)]
    [Fintype (F.obj X ⟶ F.obj X')] [Fintype (X' ⟶ X')] [Fintype (F.obj X' ⟶ F.obj X')]
    {η : ℝ} (hη : 0 ≤ η) (hη₁ : η < 1)
    (himage : Nonempty (F.obj X ⟶ F.obj X'))
    (hratio : (arrowCount (F.obj X) : ℝ) ≤ (1 + η) * arrowCount X)
    (hratio' : (arrowCount (F.obj X') : ℝ) ≤ (1 + η) * arrowCount X') :
    Function.Bijective (F.map : (X ⟶ X') → (F.obj X ⟶ F.obj X')) := by
  have hsmall : ((FiniteGroupoid.orbit (F.obj X)).card : ℝ) <
      (1 - 0) * ((FiniteGroupoid.orbit X).card + (FiniteGroupoid.orbit X').card) :=
    card_orbit_lt_of_arrowCount (ζ := 0) F.obj (by linarith) himage
      (FiniteGroupoid.card_hom_le_of_faithful F X X)
      (FiniteGroupoid.card_hom_le_of_faithful F X' X') hratio hratio'
  have hsmall' : ((FiniteGroupoid.orbit (F.obj X)).card : ℝ) <
      (FiniteGroupoid.orbit X).card + (FiniteGroupoid.orbit X').card := by
    linarith
  have horbit : (FiniteGroupoid.orbit (F.obj X)).card <
      (FiniteGroupoid.orbit X).card + (FiniteGroupoid.orbit X').card := by
    exact_mod_cast hsmall'
  exact CountingEndgame.map_bijective_of_counts F hobj himage horbit
    (card_vertexGroup_lt_two_mul_of_injective F hobj hη hη₁ hratio)

end ArrowCountMedian
end GroupApproximation
