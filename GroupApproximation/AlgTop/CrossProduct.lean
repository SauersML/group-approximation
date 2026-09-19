import GroupApproximation.AlgTop.CupProduct

/-!
# The external (cross) product in singular cohomology

For spaces `X` and `Y` the **cross product**

```text
a × b := pr₁^* a ⌣ pr₂^* b  ∈  H^{p+q}(X × Y; R)
```

is the external pairing that writes down classes on a product from classes on the
factors. It is what the counterexample programme uses to name the generators of
`H^*(S¹ × S⁵ × ∏ ℂP^{d_j}; ℤ)`, so it is built here directly out of the pullback
and the cup product, independently of the Künneth *theorem* (which asserts that
these classes span, and is a much deeper statement).

## Main definitions

* `prodMap f g` — the product of two continuous maps as a `TopCat` morphism.
* `cross a b` — the cross product, with notation `a ×ᶜ b`.

## Main results

* `cross_add_left`, `cross_add_right`, `cross_smul_left`, `cross_smul_right` —
  `R`-bilinearity.
* `cross_natural` — naturality: `(f × g)^*(a × b) = f^* a × g^* b`.
* `cross_one_right` — `a × 1 = pr₁^* a` (cast-free, since `p + 0` is `p`).

## Not here

The multiplicativity of the cross product,
`(a × b) ⌣ (a' × b') = (-1)^{q·p'} (a ⌣ a') × (b ⌣ b')`, needs to commute
`pr₂^* b` past `pr₁^* a'`, i.e. it needs **graded commutativity** of the cup
product. That identity is not available: the Alexander–Whitney diagonal is not
cocommutative on the nose, and the proof requires the Eilenberg–Zilber chain
homotopy between `Δ` and `T ∘ Δ`. The special case where one of the two inner
degrees is zero is recorded below and needs no commutativity.
-/

open CategoryTheory Limits AlgebraicTopology
open GroupApproximation.ThirdParty.HamSandwich.SphereOddDegree

namespace GroupApproximation.AlgTop

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

noncomputable section

/-! ## 1. Products of spaces and maps -/

/-- The product `X × Y` as an object of `TopCat`. -/
abbrev prodTop (X Y : TopCat.{0}) : TopCat.{0} := TopCat.of (X × Y)

/-- The product of two continuous maps, as a `TopCat` morphism
`X × Y ⟶ X' × Y'`. -/
def prodMap {X X' Y Y' : TopCat.{0}} (f : X ⟶ X') (g : Y ⟶ Y') :
    prodTop X Y ⟶ prodTop X' Y' :=
  TopCat.ofHom (ContinuousMap.prodMap f.hom g.hom)

@[simp] theorem prodMap_comp_fst {X X' Y Y' : TopCat.{0}} (f : X ⟶ X') (g : Y ⟶ Y') :
    prodMap f g ≫ TopCat.prodFst = (TopCat.prodFst : prodTop X Y ⟶ X) ≫ f := rfl

@[simp] theorem prodMap_comp_snd {X X' Y Y' : TopCat.{0}} (f : X ⟶ X') (g : Y ⟶ Y') :
    prodMap f g ≫ TopCat.prodSnd = (TopCat.prodSnd : prodTop X Y ⟶ Y) ≫ g := rfl

/-! ## 2. The cross product -/

variable {R : Type} [CommRing R]

/-- The **cross product** `Hᵖ(X; R) → H^q(Y; R) → H^{p+q}(X × Y; R)`,
`a × b = pr₁^* a ⌣ pr₂^* b`. -/
def cross {X Y : TopCat.{0}} {p q : ℕ} (a : cohomology R X p) (b : cohomology R Y q) :
    cohomology R (prodTop X Y) (p + q) :=
  (cohPullback R (TopCat.prodFst : prodTop X Y ⟶ X) p).hom a
    ⌣ (cohPullback R (TopCat.prodSnd : prodTop X Y ⟶ Y) q).hom b

@[inherit_doc] infixl:70 " ×ᶜ " => cross

/-! ## 3. Bilinearity -/

theorem cross_add_left {X Y : TopCat.{0}} {p q : ℕ} (a a' : cohomology R X p)
    (b : cohomology R Y q) : (a + a') ×ᶜ b = a ×ᶜ b + a' ×ᶜ b := by
  unfold cross
  rw [map_add, cup_add_left]

theorem cross_add_right {X Y : TopCat.{0}} {p q : ℕ} (a : cohomology R X p)
    (b b' : cohomology R Y q) : a ×ᶜ (b + b') = a ×ᶜ b + a ×ᶜ b' := by
  unfold cross
  rw [map_add, cup_add_right]

theorem cross_smul_left {X Y : TopCat.{0}} {p q : ℕ} (s : R) (a : cohomology R X p)
    (b : cohomology R Y q) : (s • a) ×ᶜ b = s • (a ×ᶜ b) := by
  unfold cross
  rw [map_smul, cup_smul_left]

theorem cross_smul_right {X Y : TopCat.{0}} {p q : ℕ} (s : R) (a : cohomology R X p)
    (b : cohomology R Y q) : a ×ᶜ (s • b) = s • (a ×ᶜ b) := by
  unfold cross
  rw [map_smul, cup_smul_right]

@[simp] theorem zero_cross {X Y : TopCat.{0}} {p q : ℕ} (b : cohomology R Y q) :
    (0 : cohomology R X p) ×ᶜ b = 0 := by
  unfold cross
  rw [map_zero, zero_cup]

@[simp] theorem cross_zero {X Y : TopCat.{0}} {p q : ℕ} (a : cohomology R X p) :
    a ×ᶜ (0 : cohomology R Y q) = 0 := by
  unfold cross
  rw [map_zero, cup_zero]

/-! ## 4. Naturality -/

/-- **Naturality of the cross product.** `(f × g)^*(a × b) = f^* a × g^* b`. -/
theorem cross_natural {X X' Y Y' : TopCat.{0}} (f : X ⟶ X') (g : Y ⟶ Y') {p q : ℕ}
    (a : cohomology R X' p) (b : cohomology R Y' q) :
    (cohPullback R (prodMap f g) (p + q)).hom (a ×ᶜ b)
      = (cohPullback R f p).hom a ×ᶜ (cohPullback R g q).hom b := by
  unfold cross
  rw [cohPullback_cup]
  congr 1
  · have h : (cohPullback R (prodMap f g ≫ TopCat.prodFst) p).hom a
        = (cohPullback R (prodMap f g) p).hom
            ((cohPullback R (TopCat.prodFst : prodTop X' Y' ⟶ X') p).hom a) := by
      rw [cohPullback_comp]; rfl
    have h' : (cohPullback R ((TopCat.prodFst : prodTop X Y ⟶ X) ≫ f) p).hom a
        = (cohPullback R (TopCat.prodFst : prodTop X Y ⟶ X) p).hom
            ((cohPullback R f p).hom a) := by
      rw [cohPullback_comp]; rfl
    rw [← h', ← h, prodMap_comp_fst]
  · have h : (cohPullback R (prodMap f g ≫ TopCat.prodSnd) q).hom b
        = (cohPullback R (prodMap f g) q).hom
            ((cohPullback R (TopCat.prodSnd : prodTop X' Y' ⟶ Y') q).hom b) := by
      rw [cohPullback_comp]; rfl
    have h' : (cohPullback R ((TopCat.prodSnd : prodTop X Y ⟶ Y) ≫ g) q).hom b
        = (cohPullback R (TopCat.prodSnd : prodTop X Y ⟶ Y) q).hom
            ((cohPullback R g q).hom b) := by
      rw [cohPullback_comp]; rfl
    rw [← h', ← h, prodMap_comp_snd]

/-! ## 5. Units and the degree-zero multiplicativity -/

/-- Crossing with the unit class on the right is the first pullback. No degree
cast appears, since `p + 0` reduces to `p`. -/
@[simp] theorem cross_one_right {X Y : TopCat.{0}} {p : ℕ} (a : cohomology R X p) :
    a ×ᶜ one R Y = (cohPullback R (TopCat.prodFst : prodTop X Y ⟶ X) p).hom a := by
  unfold cross
  rw [cohPullback_one, cup_one]

end

end GroupApproximation.AlgTop
