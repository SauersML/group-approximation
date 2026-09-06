import GroupApproximation.CharClass.SteenrodFourfoldBSwap

/-!
# The diagonal as a sum of decomposables

The evaluation of the second composite needs each `Φ` value presented as a sum of
decomposables of the pair complex, so that the fourfold functional can be
factored through the two pair functionals.

Everything here is already true by construction; the content is only that the
two presentations of one cut are the same term.  A cut of a simplex contributes a
single basis element of the pair index, and a single basis element of the pair
index *is* a decomposable of two singles.

## Main results

* `cellPair_single_tenElt` — one basis pair, as a decomposable.
* `cellPair_facePair` — one cut, as a decomposable, with its two vanishing cases.
* `cellPair_steenrodDiag`, `phiAtDeg_eq_sum` — the diagonal as a sum over
  bidegrees and cuts.
-/

open CategoryTheory
open GroupApproximation.ThirdParty.HamSandwich.SphereOddDegree
open GroupApproximation.ThirdParty.HamSandwich.SphereOddDegree.AlexanderWhitney

namespace GroupApproximation
namespace CharClass
namespace Steenrod

noncomputable section

/-- A basis pair of simplices, placed in the pair index, is the decomposable of
the two singles. -/
theorem cellPair_single_tenElt (X : TopCat.{0}) (m a b : ℕ) (h : a + b = m)
    (ρ : singularSimplices X a) (τ : singularSimplices X b) :
    cellPair X m a b (Finsupp.single (ρ, τ) 1)
      = tenElt (singFreeCx X) (singFreeCx X) (⟨(a, b), h⟩ : PairDeg m)
          (Finsupp.single ρ 1) (Finsupp.single τ 1) := by
  rw [cellPair_single_one, padIdx_of_eq h]
  exact (tenElt_single_single (singFreeCx X) (singFreeCx X)
    (⟨(a, b), h⟩ : PairDeg m) ρ τ).symm

/-- One cut, as a decomposable of the two faces it cuts out. -/
theorem cellPair_facePair (X : TopCat.{0}) (m a b : ℕ) (h : a + b = m) {N : ℕ}
    (σ : singularSimplices X N) {A B : Finset (Fin (N + 1))}
    (hA : A.card = a + 1) (hB : B.card = b + 1) :
    cellPair X m a b (facePair a b σ A B)
      = tenElt (singFreeCx X) (singFreeCx X) (⟨(a, b), h⟩ : PairDeg m)
          (Finsupp.single (restrictSimplex (faceOfFinset A hA) σ) 1)
          (Finsupp.single (restrictSimplex (faceOfFinset B hB) σ) 1) := by
  rw [facePair_of_card a b σ hA hB]
  exact cellPair_single_tenElt X m a b h _ _

theorem cellPair_facePair_left_zero (X : TopCat.{0}) (m a b : ℕ) {N : ℕ}
    (σ : singularSimplices X N) {A B : Finset (Fin (N + 1))}
    (hA : ¬ A.card = a + 1) :
    cellPair X m a b (facePair a b σ A B) = 0 := by
  rw [facePair_eq_zero_left a b σ hA]
  exact map_zero (cellPair X m a b)

theorem cellPair_facePair_right_zero (X : TopCat.{0}) (m a b : ℕ) {N : ℕ}
    (σ : singularSimplices X N) {A B : Finset (Fin (N + 1))}
    (hB : ¬ B.card = b + 1) :
    cellPair X m a b (facePair a b σ A B) = 0 := by
  rw [facePair_eq_zero_right a b σ hB]
  exact map_zero (cellPair X m a b)

/-- One bidegree of the diagonal, as a sum over the cut sets. -/
theorem cellPair_steenrodDiag (X : TopCat.{0}) (m a b j : ℕ) {N : ℕ}
    (σ : singularSimplices X N) :
    cellPair X m a b (steenrodDiag j a b σ)
      = ∑ S ∈ cutIndex (j + 1) N, cellPair X m a b (facePair a b σ (cutU S) (cutV S)) := by
  unfold steenrodDiag
  exact map_sum (cellPair X m a b) _ _

/-- **The diagonal as a sum over bidegrees**, which with the previous lemma
presents it as a sum of decomposables, one per bidegree and cut. -/
theorem phiAtDeg_eq_sum (X : TopCat.{0}) (m j : ℕ) {N : ℕ}
    (σ : singularSimplices X N) :
    phiAtDeg X m j σ
      = ∑ a ∈ Finset.range (m + 1), cellPair X m a (m - a) (steenrodDiag j a (m - a) σ) :=
  rfl

end

end Steenrod
end CharClass
end GroupApproximation
