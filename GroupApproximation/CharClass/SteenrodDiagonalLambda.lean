import GroupApproximation.CharClass.SteenrodDiagonal
import GroupApproximation.CharClass.SteenrodCupEdge
import Mathlib.LinearAlgebra.Finsupp.LinearCombination

/-!
# Steenrod's diagonal over the group ring

`cc-cartan`'s acyclic-models comparison wants Steenrod's diagonal as a map of
free modules over `Λ = F₂[ℤ/2]`, not over `F₂` one bidegree at a time.  This file
is the `Λ`-side packaging of `CharClass/SteenrodDiagonal.lean`, built against the
carriers the lead ruled on: the source free on `WSIndex`, the target free on
pairs of singular simplices whose dimensions sum to the degree, and the
involution the honest factor swap.

## The two index types

```text
WSIndex X k   = Σ n : Fin (k+1), (an n-simplex of X)          -- (W ⊗ S X)_k
PairIndex X k = Σ a : Fin (k+1), (an a-simplex) × (a (k−a)-simplex)   -- (S X ⊗ S X)_k
```

Both index by *one* degree and derive the other, following `cc-cartan`'s
`WSIndex`: with the other convention the differential needs a transport of a
simplex along an equality of degrees, and a proof argument inside a definition
blocks every later rewrite.  The `W`-index of the basis element `⟨n, σ⟩` in
degree `k` is the derived quantity `k − n`.

## Why the bidegrees line up

`steenrodDiag i a b σ` for `σ` of dimension `n` vanishes unless `a + b = n + i`,
because the two alternating families of an `i`-cut satisfy
`|cutU| + |cutV| = (n+1) + (i+1)`.  At `i = k − n` that reads `a + b = k`, which
is exactly the constraint defining `PairIndex X k`.  So `phiBasis` may sum over
all of `Fin (k+1)` with nothing dropped and nothing double counted.

## Coefficients

`Λ` is any commutative `F₂`-algebra and the coefficient map is `algebraMap`;
`cc-cartan`'s `GroupRingZ2 = MonoidAlgebra (ZMod 2) (Multiplicative (ZMod 2))`
is one.  `Φ` is `F₂`-linear and equivariant, hence `Λ`-linear, and since the
source is *free* over `Λ` on `WSIndex` the `Λ`-linear extension from the basis is
the whole of `Λ`-linearity: `Finsupp.linearCombination` supplies it.
-/

open CategoryTheory
open GroupApproximation.ThirdParty.HamSandwich.SphereOddDegree

namespace GroupApproximation
namespace CharClass
namespace Steenrod

noncomputable section

variable {X : TopCat.{0}} {Λ : Type} [CommRing Λ] [Algebra (ZMod 2) Λ]

/-! ## 1. The two index types -/

/-- The basis of `(W ⊗ S(X))_k`: an `n`-simplex with `n ≤ k`, the `W`-index being
the derived `k − n`. -/
def WSIndex (X : TopCat.{0}) (k : ℕ) : Type :=
  Σ n : Fin (k + 1), singularSimplices X n.val

/-- The basis of `(S(X) ⊗ S(X))_k`: a pair of simplices of dimensions `a` and
`k − a`. -/
def PairIndex (X : TopCat.{0}) (k : ℕ) : Type :=
  Σ a : Fin (k + 1), singularSimplices X a.val × singularSimplices X (k - a.val)

/-! ## 2. Injecting one bidegree -/

/-- Put a bidegree-`(a, k−a)` piece of the `F₂`-valued diagonal into the
`Λ`-valued degree-`k` module. -/
def injectPair (X : TopCat.{0}) (Λ : Type) [CommRing Λ] [Algebra (ZMod 2) Λ]
    {k : ℕ} (a : Fin (k + 1)) (z : tensorTwo X a.val (k - a.val)) :
    PairIndex X k →₀ Λ :=
  Finsupp.mapDomain (fun p => ⟨a, p⟩)
    (Finsupp.mapRange (algebraMap (ZMod 2) Λ) (map_zero _) z)

theorem injectPair_single (X : TopCat.{0}) (Λ : Type) [CommRing Λ] [Algebra (ZMod 2) Λ]
    {k : ℕ} (a : Fin (k + 1))
    (p : singularSimplices X a.val × singularSimplices X (k - a.val)) (c : ZMod 2) :
    injectPair X Λ a (Finsupp.single p c)
      = Finsupp.single (⟨a, p⟩ : PairIndex X k) (algebraMap (ZMod 2) Λ c) := by
  unfold injectPair
  rw [Finsupp.mapRange_single, Finsupp.mapDomain_single]
  rfl

/-! ## 3. The diagonal on the basis -/

/-- **Steenrod's diagonal on a basis element** of `(W ⊗ S(X))_k`: the sum, over
the bidegrees `a + (k − a) = k`, of the cut diagonal at the derived `W`-index. -/
def phiBasis (X : TopCat.{0}) (Λ : Type) [CommRing Λ] [Algebra (ZMod 2) Λ]
    {k : ℕ} (b : WSIndex X k) : PairIndex X k →₀ Λ :=
  ∑ a : Fin (k + 1),
    injectPair X Λ a (steenrodDiag (k - b.1.val) a.val (k - a.val) b.2)

/-- **The diagonal**, `Λ`-linear on the free module.  Since the source is free
over `Λ` on `WSIndex`, `Λ`-linearity is exactly the extension from the basis, so
the equivariance of the underlying `F₂`-map is built in rather than an extra
obligation. -/
def Phi (X : TopCat.{0}) (Λ : Type) [CommRing Λ] [Algebra (ZMod 2) Λ] (k : ℕ) :
    (WSIndex X k →₀ Λ) →ₗ[Λ] (PairIndex X k →₀ Λ) :=
  Finsupp.linearCombination Λ (phiBasis X Λ)

@[simp] theorem Phi_single (X : TopCat.{0}) (Λ : Type) [CommRing Λ] [Algebra (ZMod 2) Λ]
    (k : ℕ) (b : WSIndex X k) (c : Λ) :
    Phi X Λ k (Finsupp.single b c) = c • phiBasis X Λ b := by
  unfold Phi
  simp

theorem Phi_single_one (X : TopCat.{0}) (Λ : Type) [CommRing Λ] [Algebra (ZMod 2) Λ]
    (k : ℕ) (b : WSIndex X k) :
    Phi X Λ k (Finsupp.single b 1) = phiBasis X Λ b := by
  rw [Phi_single, one_smul]

/-! ## 4. The degree-zero normalisation -/

/-- In degree `0` the only cut of a `0`-simplex uses its single vertex for both
families, so the diagonal is the literal `x ⊗ x`. -/
theorem steenrodDiag_degree_zero (x : singularSimplices X 0) :
    steenrodDiag 0 0 0 x = Finsupp.single (x, x) 1 := by
  unfold steenrodDiag
  rw [cutIndex_self 0, Finset.sum_singleton, cutU_univ 0, cutV_univ 0]
  unfold facePair
  have hcard : (Finset.univ : Finset (Fin 1)).card = 0 + 1 := by
    rw [Finset.card_univ, Fintype.card_fin]
  rw [dif_pos hcard, dif_pos hcard, faceOfFinset_univ, restrictSimplex_id]

/-- **`phi_zero`.**  On the degree-`0` basis, the diagonal is `x ⊗ x`. -/
theorem phiBasis_degree_zero (X : TopCat.{0}) (Λ : Type) [CommRing Λ] [Algebra (ZMod 2) Λ]
    (x : singularSimplices X 0) :
    phiBasis X Λ (⟨0, x⟩ : WSIndex X 0)
      = Finsupp.single (⟨0, (x, x)⟩ : PairIndex X 0) 1 := by
  unfold phiBasis
  rw [Fin.sum_univ_one]
  show injectPair X Λ (0 : Fin (0 + 1)) (steenrodDiag 0 0 0 x) = _
  rw [steenrodDiag_degree_zero x]
  have hval := injectPair_single X Λ (0 : Fin (0 + 1)) (x, x) 1
  rw [map_one] at hval
  exact hval

end

end Steenrod
end CharClass
end GroupApproximation
