import GroupApproximation.CharClass.SteenrodFourfoldB

/-!
# The two engines of the chain-map computation for `B`

The chain-map property of the second composite is the one genuine computation in
this lane's part of the Cartan comparison.  It turns on exactly two facts, and
this file isolates both so that the computation itself is bookkeeping.

**The boundary identity for `Φ` at an explicit index.**  `dTgt_phiPair` is stated
on the published basis, where the `W`-index is the derived quantity `k - n`.  The
second composite needs it at an index and a total degree that are *free
parameters*, because its terms are `Φ(e_p ⊗ σ')` for `σ'` of a degree that varies
across the sum.  Both readings are the same theorem; `phiAtDeg` is the free-index
form and the two cases below are `chainmap_case_mid` and `chainmap_case_last`
spent on it.

**The Leibniz rule for the fourfold.**  `tensorD` on a decomposable is the
boundary in one factor plus the boundary in the other, which is `cc-cartan`'s
`tensorD_tenElt`.  Here it is transported to the totalised `padFour`, where the
degree constraint is absorbed rather than carried, so that the edge cases of the
double sum need no side conditions.

## Main results

* `dTgt_phiAtDeg_succ`, `dTgt_phiAtDeg_zero` — the boundary identity at a free
  index, with and without the `(1 + T)` term.
* `padFourL`, `padFourR`, `tensorD_padFour` — the Leibniz rule, totalised.
-/

open CategoryTheory
open GroupApproximation.ThirdParty.HamSandwich.SphereOddDegree
open GroupApproximation.ThirdParty.HamSandwich.SphereOddDegree.AlexanderWhitney

namespace GroupApproximation
namespace CharClass
namespace Steenrod

noncomputable section

/-! ## 1. The boundary identity at a free index -/

/-- **The boundary identity for `Φ` at index `i + 1`.**  The `(1 + T)` term is
present exactly because the index is a successor. -/
theorem dTgt_phiAtDeg_succ (X : TopCat.{0}) (k i M : ℕ)
    (σ : singularSimplices X (M + 1)) :
    dTgt X (ZMod 2) k (phiAtDeg X (k + 1) (i + 1) σ)
      = (phiAtDeg X k i σ + swapEnd X k (phiAtDeg X k i σ))
        + ∑ jj : Fin (M + 2), phiAtDeg X k (i + 1) (faceSimplex X M jj σ) := by
  unfold phiAtDeg
  rw [dTgt_phiSum k (i + 1) σ]
  exact chainmap_case_mid k i M (i + 1) (i + 1) rfl rfl σ

/-- **The boundary identity at index `0`.**  At the Alexander–Whitney end there
is no `(1 + T)` term. -/
theorem dTgt_phiAtDeg_zero (X : TopCat.{0}) (k M : ℕ)
    (σ : singularSimplices X (M + 1)) :
    dTgt X (ZMod 2) k (phiAtDeg X (k + 1) 0 σ)
      = ∑ jj : Fin (M + 2), phiAtDeg X k 0 (faceSimplex X M jj σ) := by
  unfold phiAtDeg
  rw [dTgt_phiSum k 0 σ]
  exact chainmap_case_last k M 0 0 rfl rfl σ

/-! ## 2. The Leibniz rule, totalised

`padFourL` and `padFourR` are defined through `cc-cartan`'s `tdL` and `tdR`
rather than through `dTgt`, so that the Leibniz rule needs no reduction of the
structure projection `(pairFreeCx X).d`.  Forcing that projection is what makes
the elaborator time out: `tensorFreeCx` is a structure literal whose
`d_d` field is a large proof.  The bridge to `dTgt` is spent once, at the end,
and nowhere else. -/

/-- The boundary in the first block of a decomposable, and `0` off the diagonal
of degrees. -/
noncomputable def padFourL (X : TopCat.{0}) (k a b : ℕ)
    (u : PairIdx X a →₀ ZMod 2) (v : PairIdx X b →₀ ZMod 2) :
    TensorIdx (pairFreeCx X) (pairFreeCx X) k →₀ ZMod 2 :=
  if h : a + b = k + 1 then tdL (pairFreeCx X) (pairFreeCx X) k a b h u v else 0

/-- The boundary in the second block. -/
noncomputable def padFourR (X : TopCat.{0}) (k a b : ℕ)
    (u : PairIdx X a →₀ ZMod 2) (v : PairIdx X b →₀ ZMod 2) :
    TensorIdx (pairFreeCx X) (pairFreeCx X) k →₀ ZMod 2 :=
  if h : a + b = k + 1 then tdR (pairFreeCx X) (pairFreeCx X) k a b h u v else 0

theorem padFourL_of_eq {X : TopCat.{0}} {k a b : ℕ} (h : a + b = k + 1)
    (u : PairIdx X a →₀ ZMod 2) (v : PairIdx X b →₀ ZMod 2) :
    padFourL X k a b u v = tdL (pairFreeCx X) (pairFreeCx X) k a b h u v :=
  dif_pos h

theorem padFourL_of_ne {X : TopCat.{0}} {k a b : ℕ} (h : ¬ a + b = k + 1)
    (u : PairIdx X a →₀ ZMod 2) (v : PairIdx X b →₀ ZMod 2) :
    padFourL X k a b u v = 0 :=
  dif_neg h

theorem padFourR_of_eq {X : TopCat.{0}} {k a b : ℕ} (h : a + b = k + 1)
    (u : PairIdx X a →₀ ZMod 2) (v : PairIdx X b →₀ ZMod 2) :
    padFourR X k a b u v = tdR (pairFreeCx X) (pairFreeCx X) k a b h u v :=
  dif_pos h

theorem padFourR_of_ne {X : TopCat.{0}} {k a b : ℕ} (h : ¬ a + b = k + 1)
    (u : PairIdx X a →₀ ZMod 2) (v : PairIdx X b →₀ ZMod 2) :
    padFourR X k a b u v = 0 :=
  dif_neg h

/-- **The Leibniz rule for the fourfold**, on a totalised decomposable, with no
degree side condition on either side. -/
theorem tensorD_padFour (X : TopCat.{0}) (k a b : ℕ)
    (u : PairIdx X a →₀ ZMod 2) (v : PairIdx X b →₀ ZMod 2) :
    tensorD (pairFreeCx X) (pairFreeCx X) k (padFour X (k + 1) a b u v)
      = padFourL X k a b u v + padFourR X k a b u v := by
  by_cases h : a + b = k + 1
  · rw [padFour_of_eq h, padFourL_of_eq h, padFourR_of_eq h]
    exact tensorD_tenElt (pairFreeCx X) (pairFreeCx X) k a b h u v
  · rw [padFour_of_ne h, padFourL_of_ne h, padFourR_of_ne h, add_zero]
    exact map_zero (tensorD (pairFreeCx X) (pairFreeCx X) k)

theorem padFourL_zero_deg (X : TopCat.{0}) (k b : ℕ)
    (u : PairIdx X 0 →₀ ZMod 2) (v : PairIdx X b →₀ ZMod 2) :
    padFourL X k 0 b u v = 0 := by
  by_cases h : 0 + b = k + 1
  · rw [padFourL_of_eq h]
    exact tdL_zero (pairFreeCx X) (pairFreeCx X) k b h u v
  · exact padFourL_of_ne h u v

theorem padFourR_zero_deg (X : TopCat.{0}) (k a : ℕ)
    (u : PairIdx X a →₀ ZMod 2) (v : PairIdx X 0 →₀ ZMod 2) :
    padFourR X k a 0 u v = 0 := by
  by_cases h : a + 0 = k + 1
  · rw [padFourR_of_eq h]
    exact tdR_zero (pairFreeCx X) (pairFreeCx X) k a h u v
  · exact padFourR_of_ne h u v

end

end Steenrod
end CharClass
end GroupApproximation
