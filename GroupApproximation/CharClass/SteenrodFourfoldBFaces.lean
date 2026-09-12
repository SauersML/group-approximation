import GroupApproximation.CharClass.SteenrodFourfoldBGeneric

/-!
# The faces are the differential of the pair complex

Each of the three branches leaves behind a family of face terms.  This file
identifies those families with the two halves of the pair complex's differential,
evaluated on the basis element the branch was about, and then assembles the three
branches into one identity valid at every basis element.

The identification is the same computation on both sides: the face contribution
is a sum over the faces of one simplex, pushed into the fourfold; and `dLeft`,
`dRight` are exactly sums over those faces of basis elements of the pair complex.
The only work is pulling the sum out of the slot of `padFour` it sits in.

## Main results

* `faceL_eq_linearCombination`, `faceR_eq_linearCombination` — the two faces.
* `sum_tensorD_compBPre` — **the chain-map identity at one basis element**, with
  the three branches assembled.
-/

open CategoryTheory
open GroupApproximation.ThirdParty.HamSandwich.SphereOddDegree
open GroupApproximation.ThirdParty.HamSandwich.SphereOddDegree.AlexanderWhitney

namespace GroupApproximation
namespace CharClass
namespace Steenrod

noncomputable section

/-! ## Sums through the two slots of `padFour` -/

/-- `padFour` in its front slot, bundled so that `map_sum` applies. -/
def padFourLeftHom (X : TopCat.{0}) (k a b : ℕ) (v : PairIdx X b →₀ ZMod 2) :
    (PairIdx X a →₀ ZMod 2) →+ (TensorIdx (pairFreeCx X) (pairFreeCx X) k →₀ ZMod 2) where
  toFun u := padFour X k a b u v
  map_zero' := padFour_zero_left k a b v
  map_add' u u' := padFour_add_left k a b u u' v

/-- `padFour` in its back slot, bundled so that `map_sum` applies. -/
def padFourRightHom (X : TopCat.{0}) (k a b : ℕ) (u : PairIdx X a →₀ ZMod 2) :
    (PairIdx X b →₀ ZMod 2) →+ (TensorIdx (pairFreeCx X) (pairFreeCx X) k →₀ ZMod 2) where
  toFun v := padFour X k a b u v
  map_zero' := padFour_zero_right k a b u
  map_add' v v' := padFour_add_right k a b u v v'

theorem padFour_sum_left {X : TopCat.{0}} (k a b : ℕ) {ι : Type} [Fintype ι]
    (u : ι → (PairIdx X a →₀ ZMod 2)) (v : PairIdx X b →₀ ZMod 2) :
    padFour X k a b (∑ j : ι, u j) v = ∑ j : ι, padFour X k a b (u j) v :=
  map_sum (padFourLeftHom X k a b v) u Finset.univ

theorem padFour_sum_right {X : TopCat.{0}} (k a b : ℕ) {ι : Type} [Fintype ι]
    (u : PairIdx X a →₀ ZMod 2) (v : ι → (PairIdx X b →₀ ZMod 2)) :
    padFour X k a b u (∑ j : ι, v j) = ∑ j : ι, padFour X k a b u (v j) :=
  map_sum (padFourRightHom X k a b u) v Finset.univ

/-- A linear combination along a sum of basis elements is the sum of the values. -/
theorem linearCombination_sum_single {α M : Type} [AddCommGroup M] [Module (ZMod 2) M]
    (g : α → M) {ι : Type} [Fintype ι] (q : ι → α) :
    Finsupp.linearCombination (ZMod 2) g (∑ j : ι, Finsupp.single (q j) (1 : ZMod 2))
      = ∑ j : ι, g (q j) := by
  have hs : ∀ a : α,
      Finsupp.linearCombination (ZMod 2) g (Finsupp.single a (1 : ZMod 2)) = g a := by
    intro a
    simp
  rw [map_sum]
  exact Finset.sum_congr rfl fun j _ => hs (q j)

/-! ## The two face families -/

/-- **The faces of the front simplex are `∂ ⊗ 1`.**  The back degree is free, so
this one statement serves the generic branch and the back-degenerate one. -/
theorem faceL_eq_linearCombination (X : TopCat.{0}) (k I M M' d p : ℕ)
    (h : M' + 1 + d = M + 1)
    (ρ : singularSimplices X (M' + 1)) (τ : singularSimplices X d) :
    faceLAt X k (d + (I - p)) p (I - p) M' ρ τ (M' + p)
      = Finsupp.linearCombination (ZMod 2) (compBPre X k I p M)
          (dLeft X (ZMod 2) M (M' + 1) d h ρ τ) := by
  rw [faceLAt_eq, padFour_sum_left, dLeft_succ, linearCombination_sum_single]
  exact Finset.sum_congr rfl fun jj _ => rfl

/-- **The faces of the back simplex are `1 ⊗ ∂`.**  The front degree is free, so
this one statement serves the generic branch and the front-degenerate one. -/
theorem faceR_eq_linearCombination (X : TopCat.{0}) (k I M c M'' p : ℕ)
    (h : c + (M'' + 1) = M + 1)
    (ρ : singularSimplices X c) (τ : singularSimplices X (M'' + 1)) :
    faceRAt X k (c + p) p (I - p) M'' ρ τ (M'' + (I - p))
      = Finsupp.linearCombination (ZMod 2) (compBPre X k I p M)
          (dRight X (ZMod 2) M c (M'' + 1) h ρ τ) := by
  rw [faceRAt_eq, Finset.smul_sum, padFour_sum_right, dRight_succ,
    linearCombination_sum_single]
  exact Finset.sum_congr rfl fun jj _ => rfl

/-! ## The three branches, assembled -/

/-- **The chain-map identity at one basis element of the pair complex.**  The
case split is on which of the two simplices is a point; the fourth combination is
impossible because the two degrees sum to a successor. -/
theorem sum_tensorD_compBPre (X : TopCat.{0}) (k i M : ℕ) (r : PairIdx X (M + 1)) :
    (∑ p ∈ Finset.range (i + 1 + 1),
        tensorD (pairFreeCx X) (pairFreeCx X) k (compBPre X (k + 1) (i + 1) p (M + 1) r))
      = ((∑ p ∈ Finset.range (i + 1), compBPre X k i p (M + 1) r)
            + innerSwapFour X k (∑ p ∈ Finset.range (i + 1), compBPre X k i p (M + 1) r))
          + ∑ p ∈ Finset.range (i + 1 + 1),
              Finsupp.linearCombination (ZMod 2) (compBPre X k (i + 1) p M)
                (dGen X (ZMod 2) M r) := by
  obtain ⟨⟨⟨c, d⟩, hcd⟩, ρ, τ⟩ := r
  cases c with
  | zero =>
      cases d with
      | zero => exact absurd hcd (by omega)
      | succ M'' =>
          have hface : (∑ p ∈ Finset.range (i + 1 + 1),
                Finsupp.linearCombination (ZMod 2) (compBPre X k (i + 1) p M)
                  (dGen X (ZMod 2) M ⟨⟨(0, M'' + 1), hcd⟩, (ρ, τ)⟩))
              = ∑ p ∈ Finset.range (i + 1 + 1),
                  faceRAt X k (0 + p) p (i + 1 - p) M'' ρ τ (M'' + (i + 1 - p)) := by
            refine Finset.sum_congr rfl fun p _ => ?_
            show Finsupp.linearCombination (ZMod 2) (compBPre X k (i + 1) p M)
                  (dLeft X (ZMod 2) M 0 (M'' + 1) hcd ρ τ
                    + dRight X (ZMod 2) M 0 (M'' + 1) hcd ρ τ)
                = faceRAt X k (0 + p) p (i + 1 - p) M'' ρ τ (M'' + (i + 1 - p))
            rw [dLeft_zero, zero_add,
              ← faceR_eq_linearCombination X k (i + 1) M 0 M'' p hcd ρ τ]
          rw [hface]
          exact sum_tensorD_front_zero X k i M'' ρ τ
  | succ M' =>
      cases d with
      | zero =>
          have hface : (∑ p ∈ Finset.range (i + 1 + 1),
                Finsupp.linearCombination (ZMod 2) (compBPre X k (i + 1) p M)
                  (dGen X (ZMod 2) M ⟨⟨(M' + 1, 0), hcd⟩, (ρ, τ)⟩))
              = ∑ p ∈ Finset.range (i + 1 + 1),
                  faceLAt X k (0 + (i + 1 - p)) p (i + 1 - p) M' ρ τ (M' + p) := by
            refine Finset.sum_congr rfl fun p _ => ?_
            show Finsupp.linearCombination (ZMod 2) (compBPre X k (i + 1) p M)
                  (dLeft X (ZMod 2) M (M' + 1) 0 hcd ρ τ
                    + dRight X (ZMod 2) M (M' + 1) 0 hcd ρ τ)
                = faceLAt X k (0 + (i + 1 - p)) p (i + 1 - p) M' ρ τ (M' + p)
            rw [dRight_zero, add_zero,
              ← faceL_eq_linearCombination X k (i + 1) M M' 0 p hcd ρ τ]
          rw [hface]
          exact sum_tensorD_back_zero X k i M' ρ τ
      | succ M'' =>
          have hface : (∑ p ∈ Finset.range (i + 1 + 1),
                Finsupp.linearCombination (ZMod 2) (compBPre X k (i + 1) p M)
                  (dGen X (ZMod 2) M ⟨⟨(M' + 1, M'' + 1), hcd⟩, (ρ, τ)⟩))
              = (∑ p ∈ Finset.range (i + 1 + 1),
                    faceLAt X k (M'' + 1 + (i + 1 - p)) p (i + 1 - p) M' ρ τ (M' + p))
                + ∑ p ∈ Finset.range (i + 1 + 1),
                    faceRAt X k (M' + 1 + p) p (i + 1 - p) M'' ρ τ (M'' + (i + 1 - p)) := by
            rw [← Finset.sum_add_distrib]
            refine Finset.sum_congr rfl fun p _ => ?_
            show Finsupp.linearCombination (ZMod 2) (compBPre X k (i + 1) p M)
                  (dLeft X (ZMod 2) M (M' + 1) (M'' + 1) hcd ρ τ
                    + dRight X (ZMod 2) M (M' + 1) (M'' + 1) hcd ρ τ)
                = faceLAt X k (M'' + 1 + (i + 1 - p)) p (i + 1 - p) M' ρ τ (M' + p)
                  + faceRAt X k (M' + 1 + p) p (i + 1 - p) M'' ρ τ (M'' + (i + 1 - p))
            rw [map_add, ← faceL_eq_linearCombination X k (i + 1) M M' (M'' + 1) p hcd ρ τ,
              ← faceR_eq_linearCombination X k (i + 1) M (M' + 1) M'' p hcd ρ τ]
          rw [hface]
          exact sum_tensorD_generic X k i M' M'' ρ τ

end

end Steenrod
end CharClass
end GroupApproximation
