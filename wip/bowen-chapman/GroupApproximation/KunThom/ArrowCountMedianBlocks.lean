import GroupApproximation.KunThom.ArrowCountMedian

/-!
# Arrow counts in the shape of the block median lemma

`MedianVertexForm.blockRatio_negligible` is Kun and Thom's one-sided median lemma
(arXiv:2608.06222v3, Lemma 4.4) for embedded cluster blocks.
- **Input:** one-sided inequalities `f (π i) ≤ (1 + κ) · f i`, with `κ` vanishing.
- **Output:** off negligible weight, the squared ratio bounds
  `(1 - 2η)² · f (π i) ≤ (1 + 2η)² · f i` and `(1 - 2η)² · f i ≤ (1 + 2η)² · f (π i)`.

This file converts between those shapes and the `(1 - ζ)` and `(1 + η)` forms
of `ArrowCountMedian`, so the median lemma is applied once, to `arrowCount`.

* `le_one_add_two_mul_of_one_sub_mul_le` and `arrowCount_le_of_clean`: a clean
  object `X` has `arrowCount X ≤ (1 + 2ζ) · arrowCount (f X)` for `0 ≤ ζ ≤ 1/2`.
  This is the input `hone` with `κ := 2ζ`.
* `le_one_add_mul_of_sq_mul_le` and `arrowCount_ratio_of_sqRatio`: for
  `0 ≤ η ≤ 1/16`, `(1 - 2η)² · b ≤ (1 + 2η)² · a` gives `b ≤ (1 + 16η) · a`.
* `card_vertexGroup_lt_two_mul_of_sqRatio`, `nonempty_hom_of_sqRatio` and
  `map_bijective_of_sqRatio`: the counting conclusions of `ArrowCountMedian`
  from the squared ratio bounds.  The first two need `16η + 2ζ < 1` and the
  third needs `16η < 1`.
-/

namespace GroupApproximation
namespace ArrowCountMedian

open CategoryTheory

universe u v u' v'

/-! ### Real arithmetic -/

/-- A drop by at most the factor `1 - ζ` is a rise by at most the factor
`1 + 2ζ`, for `0 ≤ ζ ≤ 1/2`. -/
theorem le_one_add_two_mul_of_one_sub_mul_le {a b ζ : ℝ} (ha : 0 ≤ a) (hζ : 0 ≤ ζ)
    (hζ₂ : ζ ≤ 1 / 2) (h : (1 - ζ) * a ≤ b) :
    a ≤ (1 + 2 * ζ) * b := by
  have h₁ : (1 + 2 * ζ) * ((1 - ζ) * a) ≤ (1 + 2 * ζ) * b :=
    mul_le_mul_of_nonneg_left h (by linarith)
  have h₂ : 0 ≤ ζ * (1 - 2 * ζ) * a := mul_nonneg (mul_nonneg hζ (by linarith)) ha
  linarith

/-- **Squared ratio to linear ratio.**  For `0 ≤ η ≤ 1/16` the squared factor
`((1 + 2η) / (1 - 2η))²` is at most `1 + 16η`. -/
theorem le_one_add_mul_of_sq_mul_le {a b η : ℝ} (ha : 0 ≤ a) (hη : 0 ≤ η)
    (hη₁ : η ≤ 1 / 16) (h : (1 - 2 * η) ^ 2 * b ≤ (1 + 2 * η) ^ 2 * a) :
    b ≤ (1 + 16 * η) * a := by
  by_contra hcon
  have hlt : (1 + 16 * η) * a < b := not_le.mp hcon
  have hsq : 0 < (1 - 2 * η) ^ 2 := pow_pos (by linarith) 2
  have h₁ : (1 - 2 * η) ^ 2 * ((1 + 16 * η) * a) < (1 - 2 * η) ^ 2 * b :=
    mul_lt_mul_of_pos_left hlt hsq
  have hη₂ : 0 ≤ η ^ 2 := sq_nonneg η
  have h₂ : 0 ≤ η * (1 - 8 * η + 8 * η ^ 2) * a :=
    mul_nonneg (mul_nonneg hη (by linarith)) ha
  linarith

/-! ### Arrow counts -/

/-- **The block median input.**  A clean object has
`arrowCount X ≤ (1 + 2ζ) · arrowCount (f X)`, which is the hypothesis `hone` of
`MedianVertexForm.blockRatio_negligible` with `κ := 2ζ`. -/
theorem arrowCount_le_of_clean {C : Type u} [Groupoid.{v} C] [Fintype C] [DecidableEq C]
    {D : Type u'} [Groupoid.{v'} D] [Fintype D]
    (R : Finset C) (f : C → D) (hinj : Set.InjOn f (R : Set C))
    (hconn : ∀ X ∈ R, ∀ Y ∈ R, Nonempty (X ⟶ Y) → Nonempty (f X ⟶ f Y))
    {X : C} (hX : X ∈ R) [Fintype (X ⟶ X)] [Fintype (f X ⟶ f X)] {ζ : ℝ}
    (hζ : 0 ≤ ζ) (hζ₂ : ζ ≤ 1 / 2)
    (hclean : ((FiniteGroupoid.orbit X \ R).card : ℝ) ≤ ζ * (FiniteGroupoid.orbit X).card)
    (hvert : Fintype.card (X ⟶ X) ≤ Fintype.card (f X ⟶ f X)) :
    (arrowCount X : ℝ) ≤ (1 + 2 * ζ) * arrowCount (f X) :=
  le_one_add_two_mul_of_one_sub_mul_le (Nat.cast_nonneg _) hζ hζ₂
    (mul_arrowCount_le_of_clean R f hinj hconn hX hclean hvert)

/-- The squared ratio bound of `MedianVertexForm.blockRatio_negligible` as a
linear ratio bound for arrow counts. -/
theorem arrowCount_ratio_of_sqRatio {C : Type u} [Groupoid.{v} C] [Fintype C]
    {D : Type u'} [Groupoid.{v'} D] [Fintype D] (f : C → D) {X : C}
    [Fintype (X ⟶ X)] [Fintype (f X ⟶ f X)] {η : ℝ} (hη : 0 ≤ η) (hη₁ : η ≤ 1 / 16)
    (hsq : (1 - 2 * η) ^ 2 * (arrowCount (f X) : ℝ) ≤ (1 + 2 * η) ^ 2 * arrowCount X) :
    (arrowCount (f X) : ℝ) ≤ (1 + 16 * η) * arrowCount X :=
  le_one_add_mul_of_sq_mul_le (Nat.cast_nonneg _) hη hη₁ hsq

/-- **Isotropy index below two from the squared ratio bound.** -/
theorem card_vertexGroup_lt_two_mul_of_sqRatio {C : Type u} [Groupoid.{v} C] [Fintype C]
    [DecidableEq C] {D : Type u'} [Groupoid.{v'} D] [Fintype D]
    (R : Finset C) (f : C → D) (hinj : Set.InjOn f (R : Set C))
    (hconn : ∀ X ∈ R, ∀ Y ∈ R, Nonempty (X ⟶ Y) → Nonempty (f X ⟶ f Y))
    {X : C} (hX : X ∈ R) [Fintype (X ⟶ X)] [Fintype (f X ⟶ f X)] {ζ η : ℝ}
    (hζ : 0 ≤ ζ) (hη : 0 ≤ η) (hηζ : 16 * η + 2 * ζ < 1)
    (hclean : ((FiniteGroupoid.orbit X \ R).card : ℝ) ≤ ζ * (FiniteGroupoid.orbit X).card)
    (hsq : (1 - 2 * η) ^ 2 * (arrowCount (f X) : ℝ) ≤ (1 + 2 * η) ^ 2 * arrowCount X) :
    Fintype.card (f X ⟶ f X) < 2 * Fintype.card (X ⟶ X) :=
  card_vertexGroup_lt_two_mul_of_arrowCount R f hinj hconn hX (by linarith) hηζ hclean
    (arrowCount_ratio_of_sqRatio f hη (by linarith) hsq)

/-- **Connectedness from the squared ratio bounds.**  Two clean objects of `R`
with connected images, whose arrow counts satisfy the squared ratio bounds, are
connected. -/
theorem nonempty_hom_of_sqRatio {C : Type u} [Groupoid.{v} C] [Fintype C] [DecidableEq C]
    {D : Type u'} [Groupoid.{v'} D] [Fintype D]
    (R : Finset C) (f : C → D) (hinj : Set.InjOn f (R : Set C))
    (hconn : ∀ X ∈ R, ∀ Y ∈ R, Nonempty (X ⟶ Y) → Nonempty (f X ⟶ f Y))
    {X X' : C} (hX : X ∈ R) (hX' : X' ∈ R)
    [Fintype (X ⟶ X)] [Fintype (f X ⟶ f X)] [Fintype (X' ⟶ X')] [Fintype (f X' ⟶ f X')]
    {ζ η : ℝ} (hζ : 0 ≤ ζ) (hη : 0 ≤ η) (hηζ : 16 * η + 2 * ζ < 1)
    (hclean : ((FiniteGroupoid.orbit X \ R).card : ℝ) ≤ ζ * (FiniteGroupoid.orbit X).card)
    (hclean' : ((FiniteGroupoid.orbit X' \ R).card : ℝ) ≤ ζ * (FiniteGroupoid.orbit X').card)
    (himage : Nonempty (f X ⟶ f X'))
    (hvert : Fintype.card (X ⟶ X) ≤ Fintype.card (f X ⟶ f X))
    (hvert' : Fintype.card (X' ⟶ X') ≤ Fintype.card (f X' ⟶ f X'))
    (hsq : (1 - 2 * η) ^ 2 * (arrowCount (f X) : ℝ) ≤ (1 + 2 * η) ^ 2 * arrowCount X)
    (hsq' : (1 - 2 * η) ^ 2 * (arrowCount (f X') : ℝ) ≤ (1 + 2 * η) ^ 2 * arrowCount X') :
    Nonempty (X ⟶ X') :=
  nonempty_hom_of_arrowCount R f hinj hconn hX hX' hηζ hclean hclean' himage hvert hvert'
    (arrowCount_ratio_of_sqRatio f hη (by linarith) hsq)
    (arrowCount_ratio_of_sqRatio f hη (by linarith) hsq')

/-- **Hom-set bijection from the squared ratio bounds.**  Let `F` be faithful and
injective on objects, and let the images of `X` and `X'` be connected.  If the
arrow counts of `X` and `X'` satisfy the squared ratio bounds with `16η < 1`, then
`F` is bijective from `X ⟶ X'` onto the image Hom-set. -/
theorem map_bijective_of_sqRatio {C : Type u} [Groupoid.{v} C] [Fintype C]
    [DecidableEq C] {D : Type u'} [Groupoid.{v'} D] [Fintype D] (F : C ⥤ D)
    [F.Faithful] (hobj : Function.Injective F.obj) {X X' : C}
    [Fintype (X ⟶ X)] [Fintype (X ⟶ X')] [Fintype (F.obj X ⟶ F.obj X)]
    [Fintype (F.obj X ⟶ F.obj X')] [Fintype (X' ⟶ X')] [Fintype (F.obj X' ⟶ F.obj X')]
    {η : ℝ} (hη : 0 ≤ η) (hη₁ : 16 * η < 1)
    (himage : Nonempty (F.obj X ⟶ F.obj X'))
    (hsq : (1 - 2 * η) ^ 2 * (arrowCount (F.obj X) : ℝ) ≤ (1 + 2 * η) ^ 2 * arrowCount X)
    (hsq' : (1 - 2 * η) ^ 2 * (arrowCount (F.obj X') : ℝ) ≤
      (1 + 2 * η) ^ 2 * arrowCount X') :
    Function.Bijective (F.map : (X ⟶ X') → (F.obj X ⟶ F.obj X')) :=
  map_bijective_of_arrowCount F hobj (by linarith) hη₁ himage
    (arrowCount_ratio_of_sqRatio F.obj hη (by linarith) hsq)
    (arrowCount_ratio_of_sqRatio F.obj hη (by linarith) hsq')

end ArrowCountMedian
end GroupApproximation
