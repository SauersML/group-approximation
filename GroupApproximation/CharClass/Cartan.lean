import GroupApproximation.CharClass.AcyclicModels
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

/-!
# The Cartan formula

The Cartan formula `Sq^k(a ⌣ b) = ∑_{i+j=k} Sq^i a ⌣ Sq^j b` is assembled from
three pieces, and this file supplies the two that do not depend on any
particular construction of the squares.

## 1. From a natural chain homotopy to an equality of cochain classes

Steenrod's squares are the cochains `σ ↦ (α ⊗ α)(Φ (e_i ⊗ σ))` obtained by
evaluating a *pair* of cocycles against an equivariant diagonal `Φ`.  Two such
diagonals — Steenrod's own and the one built out of a product decomposition —
are naturally chain homotopic by the acyclic-models theorem, and
`NaturalHomotopy.cochain_succ` turns that homotopy into the statement actually
used: the two cochains differ by an explicit coboundary, so they define the same
cohomology class.  The only hypothesis on the evaluating functional `u` is that
it annihilates boundaries, which for `u = α ⊗ β` is exactly the statement that
`α` and `β` are cocycles.

## 2. The comparison package

`DiagonalComparison` bundles the hypotheses of the acyclic-models theorem
together with the two natural transformations to be compared.  This is the
interface `cc-cartan` consumes: what is used about Steenrod's `Φ` is only that
it is natural, `Λ`-linear degreewise (which *is* the equivariance, `Λ` being the
group ring — see `AcyclicModels.lean`), a chain map, and normalized in degree
`0`.  Nothing about the explicit front/back-face formula enters.

## 3. From the cross-product Cartan formula to the cup-product one

`sq_mul_of_sq_cross` is the last mile: the diagonal `X → X × X` is a map of
spaces, so its pullback is a ring homomorphism commuting with the squares and
carrying the cross product to the cup product; the cup formula follows from the
cross formula by applying it.  Stated on *total* (ungraded) cohomology rings, so
that no degree casts appear; this is also the shape `cc-wu`'s `ParityData`
wants.
-/

universe u v w

namespace GroupApproximation.CharClass

open CategoryTheory CategoryTheory.Limits

/-! ## 1. Cochain consequences of a natural homotopy -/

section Cochain

variable {C : Type u} [Category.{v} C]
variable {Λ : Type} [CommRing Λ]
variable {F G : C ⥤ ChainComplex (ModuleCat.{0} Λ) ℕ}

/-- **Cochain form of a natural homotopy, positive degrees.**  If `u` annihilates
boundaries, the two cochains obtained by evaluating `u` against `f` and against
`g` differ by the coboundary of `s ≫ u`. -/
lemma NaturalHomotopy.cochain_succ {f g : F ⟶ G} (h : NaturalHomotopy F G f g)
    (X : C) (k : ℕ) {R : ModuleCat.{0} Λ} (u : (G.obj X).X (k + 1) ⟶ R)
    (hu : (G.obj X).d (k + 2) (k + 1) ≫ u = 0) :
    (f.app X).f (k + 1) ≫ u
      = (g.app X).f (k + 1) ≫ u + (F.obj X).d (k + 1) k ≫ (h.s k X ≫ u) := by
  have hc := congrArg (fun w : (F.obj X).X (k + 1) ⟶ (G.obj X).X (k + 1) => w ≫ u)
    (h.comm_succ k X)
  simp only [Preadditive.sub_comp, Preadditive.add_comp, Category.assoc, hu, comp_zero,
    add_zero] at hc
  rw [sub_eq_iff_eq_add] at hc
  rw [hc]
  abel

/-- **Cochain form of a natural homotopy, degree zero.**  In degree `0` there is
no room for a correcting coboundary: the two cochains are equal. -/
lemma NaturalHomotopy.cochain_zero {f g : F ⟶ G} (h : NaturalHomotopy F G f g)
    (X : C) {R : ModuleCat.{0} Λ} (u : (G.obj X).X 0 ⟶ R)
    (hu : (G.obj X).d 1 0 ≫ u = 0) :
    (f.app X).f 0 ≫ u = (g.app X).f 0 ≫ u := by
  have hc := congrArg (fun w : (F.obj X).X 0 ⟶ (G.obj X).X 0 => w ≫ u) (h.comm_zero X)
  simp only [Preadditive.sub_comp, Category.assoc, hu, comp_zero] at hc
  rw [sub_eq_zero] at hc
  exact hc

end Cochain

/-! ## 2. The comparison package -/

section Comparison

variable {C : Type u} [Category.{v} C] {ι : Type w}
variable {Λ : Type} [CommRing Λ]

/-- The input `cc-cartan` consumes: two natural transformations between functors
into chain complexes, out of a functor free on the models into one acyclic on
the models, agreeing in degree `0`.

In the Cartan application `C` is `TopCat × TopCat`, the models are the *diagonal*
models `(Δ^n, Δ^n)` (a singular `n`-simplex of `X × Y` is a pair of singular
`n`-simplices with a common domain, which is why the models are diagonal), `Λ`
is the group ring `(ZMod 2)[ℤ/2]` — so that `Λ`-linearity *is* equivariance —
`F` is `(X, Y) ↦ W ⊗ S(X × Y)` and `G` is `(X, Y) ↦ (S(X) ⊗ S(Y))^{⊗ 2}`.
`Φ₁` is Steenrod's diagonal transported through Alexander–Whitney and `Φ₂` is
the map built from the diagonals of the two factors. -/
structure DiagonalComparison (M : ι → C) (Λ : Type) [CommRing Λ]
    (F G : C ⥤ ChainComplex (ModuleCat.{0} Λ) ℕ) where
  /-- The source is free on the models. -/
  free : FreeOnModels M Λ F
  /-- The target is acyclic on the models. -/
  acyclic : AcyclicOnModels M Λ G
  /-- The first natural chain map. -/
  Φ₁ : F ⟶ G
  /-- The second natural chain map. -/
  Φ₂ : F ⟶ G
  /-- The two agree in degree `0`. -/
  agree_zero : ∀ X : C, (Φ₁.app X).f 0 = (Φ₂.app X).f 0

namespace DiagonalComparison

variable {M : ι → C} {F G : C ⥤ ChainComplex (ModuleCat.{0} Λ) ℕ}

/-- The natural chain homotopy supplied by the acyclic-models theorem. -/
noncomputable def homotopy (D : DiagonalComparison M Λ F G) :
    NaturalHomotopy F G D.Φ₁ D.Φ₂ :=
  acyclicModelsHomotopy D.free D.acyclic D.Φ₁ D.Φ₂ D.agree_zero

/-- **The Cartan comparison at the cochain level.**  Evaluating a functional that
annihilates boundaries against the two diagonals gives cochains differing by an
explicit coboundary, hence equal cohomology classes. -/
theorem cochain_succ (D : DiagonalComparison M Λ F G) (X : C) (k : ℕ)
    {R : ModuleCat.{0} Λ} (u : (G.obj X).X (k + 1) ⟶ R)
    (hu : (G.obj X).d (k + 2) (k + 1) ≫ u = 0) :
    ∃ v : (F.obj X).X k ⟶ R,
      (D.Φ₁.app X).f (k + 1) ≫ u
        = (D.Φ₂.app X).f (k + 1) ≫ u + (F.obj X).d (k + 1) k ≫ v :=
  ⟨D.homotopy.s k X ≫ u, D.homotopy.cochain_succ X k u hu⟩

/-- In degree `0` the two evaluations agree on the nose. -/
theorem cochain_zero (D : DiagonalComparison M Λ F G) (X : C)
    {R : ModuleCat.{0} Λ} (u : (G.obj X).X 0 ⟶ R)
    (hu : (G.obj X).d 1 0 ≫ u = 0) :
    (D.Φ₁.app X).f 0 ≫ u = (D.Φ₂.app X).f 0 ≫ u :=
  D.homotopy.cochain_zero X u hu

end DiagonalComparison

end Comparison

/-! ## 3. Cross Cartan implies cup Cartan -/

section LastMile

/-- **From the cross-product Cartan formula to the cup-product Cartan formula.**

`H` is the total mod-2 cohomology ring of a space `X` and `K` that of `X × X`;
`cross` is the external product and `dstar` the pullback along the diagonal,
which is a ring map carrying `cross a b` to `a * b` and commuting with the
squares.  Working with total (ungraded) rings keeps every degree cast out of the
statement, and is the shape `cc-wu` consumes. -/
theorem sq_mul_of_sq_cross {H K : Type u} [CommRing H] [CommRing K]
    (SqH : ℕ → H → H) (SqK : ℕ → K → K) (cross : H → H → K) (dstar : K →+* H)
    (hcross : ∀ a b : H, dstar (cross a b) = a * b)
    (hnat : ∀ (k : ℕ) (z : K), dstar (SqK k z) = SqH k (dstar z))
    (hcart : ∀ (k : ℕ) (a b : H),
      SqK k (cross a b) = ∑ i ∈ Finset.range (k + 1), cross (SqH i a) (SqH (k - i) b))
    (k : ℕ) (a b : H) :
    SqH k (a * b) = ∑ i ∈ Finset.range (k + 1), SqH i a * SqH (k - i) b := by
  have h1 : SqH k (a * b) = dstar (SqK k (cross a b)) := by
    rw [hnat, hcross]
  rw [h1, hcart, map_sum]
  exact Finset.sum_congr rfl fun i _ => hcross _ _

/-- The same statement with the sum indexed by the antidiagonal of `k`, which is
the form in which the Cartan formula is usually quoted. -/
theorem sq_mul_of_sq_cross' {H K : Type u} [CommRing H] [CommRing K]
    (SqH : ℕ → H → H) (SqK : ℕ → K → K) (cross : H → H → K) (dstar : K →+* H)
    (hcross : ∀ a b : H, dstar (cross a b) = a * b)
    (hnat : ∀ (k : ℕ) (z : K), dstar (SqK k z) = SqH k (dstar z))
    (hcart : ∀ (k : ℕ) (a b : H),
      SqK k (cross a b) = ∑ ij ∈ Finset.antidiagonal k, cross (SqH ij.1 a) (SqH ij.2 b))
    (k : ℕ) (a b : H) :
    SqH k (a * b) = ∑ ij ∈ Finset.antidiagonal k, SqH ij.1 a * SqH ij.2 b := by
  have h1 : SqH k (a * b) = dstar (SqK k (cross a b)) := by
    rw [hnat, hcross]
  rw [h1, hcart, map_sum]
  exact Finset.sum_congr rfl fun ij _ => hcross _ _

end LastMile

end GroupApproximation.CharClass
