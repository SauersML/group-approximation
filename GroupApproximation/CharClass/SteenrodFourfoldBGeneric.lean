import GroupApproximation.CharClass.SteenrodFourfoldBDegenCase

/-!
# The generic branch of the chain-map identity

At a bidegree of the diagonal where both simplices are positive-dimensional every
summand of the Leibniz expansion is live, and the two blocks contribute six
families in all.  Four of them are the answer: the level-`i` sum, its inner swap,
and the two families of faces.  The remaining two cancel against each other, the
left block at index `p + 1` against the right block at index `p`, and that
cancellation is `sum_cancelA_cancelB`.

Every junction where the same number arrives spelled two ways is crossed by a
named `congrArg` before any block lemma is applied, so the rewrite chains below
never normalise arithmetic.

## Main results

* `sum_tensorD_generic` — **the generic branch.**
-/

open CategoryTheory
open GroupApproximation.ThirdParty.HamSandwich.SphereOddDegree
open GroupApproximation.ThirdParty.HamSandwich.SphereOddDegree.AlexanderWhitney

namespace GroupApproximation
namespace CharClass
namespace Steenrod

noncomputable section

/-! ## The remaining junctions -/

/-- The left block read as a function of the back index alone. -/
def padFourLBack (X : TopCat.{0}) (k a p : ℕ) {c d : ℕ}
    (ρ : singularSimplices X c) (τ : singularSimplices X d) (q : ℕ) :
    TensorIdx (pairFreeCx X) (pairFreeCx X) k →₀ ZMod 2 :=
  padFourL X k a (d + q) (phiAtDeg X a p ρ)
    ((groupRingGen ^ p) • phiAtDeg X (d + q) q τ)

theorem padFourL_back_congr (X : TopCat.{0}) (k a p : ℕ) {c d : ℕ}
    (ρ : singularSimplices X c) (τ : singularSimplices X d) {q q' : ℕ} (h : q = q') :
    padFourL X k a (d + q) (phiAtDeg X a p ρ)
          ((groupRingGen ^ p) • phiAtDeg X (d + q) q τ)
      = padFourL X k a (d + q') (phiAtDeg X a p ρ)
          ((groupRingGen ^ p) • phiAtDeg X (d + q') q' τ) :=
  congrArg (padFourLBack X k a p ρ τ) h

/-- The right block read as a function of the back index alone. -/
def padFourRBack (X : TopCat.{0}) (k a p : ℕ) {c d : ℕ}
    (ρ : singularSimplices X c) (τ : singularSimplices X d) (q : ℕ) :
    TensorIdx (pairFreeCx X) (pairFreeCx X) k →₀ ZMod 2 :=
  padFourR X k a (d + q) (phiAtDeg X a p ρ)
    ((groupRingGen ^ p) • phiAtDeg X (d + q) q τ)

theorem padFourR_back_congr (X : TopCat.{0}) (k a p : ℕ) {c d : ℕ}
    (ρ : singularSimplices X c) (τ : singularSimplices X d) {q q' : ℕ} (h : q = q') :
    padFourR X k a (d + q) (phiAtDeg X a p ρ)
          ((groupRingGen ^ p) • phiAtDeg X (d + q) q τ)
      = padFourR X k a (d + q') (phiAtDeg X a p ρ)
          ((groupRingGen ^ p) • phiAtDeg X (d + q') q' τ) :=
  congrArg (padFourRBack X k a p ρ τ) h

/-- The right face contribution read as a function of the back index, the back
degree moving with it. -/
def faceRBack (X : TopCat.{0}) (k a p M'' : ℕ) {c : ℕ}
    (ρ : singularSimplices X c) (τ : singularSimplices X (M'' + 1)) (q : ℕ) :
    TensorIdx (pairFreeCx X) (pairFreeCx X) k →₀ ZMod 2 :=
  faceRAt X k a p q M'' ρ τ (M'' + q)

theorem faceRAt_back_congr (X : TopCat.{0}) (k a p M'' : ℕ) {c : ℕ}
    (ρ : singularSimplices X c) (τ : singularSimplices X (M'' + 1)) {q q' : ℕ}
    (h : q = q') :
    faceRAt X k a p q M'' ρ τ (M'' + q) = faceRAt X k a p q' M'' ρ τ (M'' + q') :=
  congrArg (faceRBack X k a p M'' ρ τ) h

/-! ## The six families at a generic bidegree -/

/-- The summand of the level-`i` sum. -/
def genB (X : TopCat.{0}) (k i M' M'' : ℕ)
    (ρ : singularSimplices X (M' + 1)) (τ : singularSimplices X (M'' + 1)) (p : ℕ) :
    TensorIdx (pairFreeCx X) (pairFreeCx X) k →₀ ZMod 2 :=
  bTerm X k (M' + 1 + p) (M'' + 1 + (i - p)) p (i - p) ρ τ

/-- The left block of the Leibniz expansion. -/
def genL (X : TopCat.{0}) (k i M' M'' : ℕ)
    (ρ : singularSimplices X (M' + 1)) (τ : singularSimplices X (M'' + 1)) (p : ℕ) :
    TensorIdx (pairFreeCx X) (pairFreeCx X) k →₀ ZMod 2 :=
  padFourL X k (M' + 1 + p) (M'' + 1 + (i - p)) (phiAtDeg X (M' + 1 + p) p ρ)
    ((groupRingGen ^ p) • phiAtDeg X (M'' + 1 + (i - p)) (i - p) τ)

/-- The right block of the Leibniz expansion. -/
def genR (X : TopCat.{0}) (k i M' M'' : ℕ)
    (ρ : singularSimplices X (M' + 1)) (τ : singularSimplices X (M'' + 1)) (p : ℕ) :
    TensorIdx (pairFreeCx X) (pairFreeCx X) k →₀ ZMod 2 :=
  padFourR X k (M' + 1 + p) (M'' + 1 + (i - p)) (phiAtDeg X (M' + 1 + p) p ρ)
    ((groupRingGen ^ p) • phiAtDeg X (M'' + 1 + (i - p)) (i - p) τ)

/-- The faces of the front simplex. -/
def genFL (X : TopCat.{0}) (k i M' M'' : ℕ)
    (ρ : singularSimplices X (M' + 1)) (τ : singularSimplices X (M'' + 1)) (p : ℕ) :
    TensorIdx (pairFreeCx X) (pairFreeCx X) k →₀ ZMod 2 :=
  faceLAt X k (M'' + 1 + (i - p)) p (i - p) M' ρ τ (M' + p)

/-- The faces of the back simplex. -/
def genFR (X : TopCat.{0}) (k i M' M'' : ℕ)
    (ρ : singularSimplices X (M' + 1)) (τ : singularSimplices X (M'' + 1)) (p : ℕ) :
    TensorIdx (pairFreeCx X) (pairFreeCx X) k →₀ ZMod 2 :=
  faceRAt X k (M' + 1 + p) p (i - p) M'' ρ τ (M'' + (i - p))

/-! ## The branch -/

/-- **The generic branch.**  At a bidegree where neither simplex is a point the
differentiated level-`i + 1` sum is the level-`i` sum, plus its inner swap, plus
the two families of faces; the two cancelling families disappear together. -/
theorem sum_tensorD_generic (X : TopCat.{0}) (k i M' M'' : ℕ)
    (ρ : singularSimplices X (M' + 1)) (τ : singularSimplices X (M'' + 1)) :
    (∑ p ∈ Finset.range (i + 1 + 1),
        tensorD (pairFreeCx X) (pairFreeCx X) k (genB X (k + 1) (i + 1) M' M'' ρ τ p))
      = ((∑ p ∈ Finset.range (i + 1), genB X k i M' M'' ρ τ p)
            + innerSwapFour X k (∑ p ∈ Finset.range (i + 1), genB X k i M' M'' ρ τ p))
          + ((∑ p ∈ Finset.range (i + 1 + 1), genFL X k (i + 1) M' M'' ρ τ p)
              + ∑ p ∈ Finset.range (i + 1 + 1), genFR X k (i + 1) M' M'' ρ τ p) := by
  -- the differential splits into the two blocks, summand by summand
  have hsplit : (∑ p ∈ Finset.range (i + 1 + 1),
        tensorD (pairFreeCx X) (pairFreeCx X) k (genB X (k + 1) (i + 1) M' M'' ρ τ p))
      = (∑ p ∈ Finset.range (i + 1 + 1), genL X k (i + 1) M' M'' ρ τ p)
        + ∑ p ∈ Finset.range (i + 1 + 1), genR X k (i + 1) M' M'' ρ τ p := by
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun p _ =>
      tensorD_bTerm X k (M' + 1 + p) (M'' + 1 + (i + 1 - p)) p (i + 1 - p) ρ τ
  -- the left block at index zero has no boundary to take but the faces
  have hL0 : genL X k (i + 1) M' M'' ρ τ 0 = genFL X k (i + 1) M' M'' ρ τ 0 :=
    padFourL_compBPre_zero X k M' _ ρ _
  -- the left block at a successor index, in three pieces
  have hLs : ∀ p ∈ Finset.range (i + 1),
      genL X k (i + 1) M' M'' ρ τ (p + 1)
        = (cancelA X k i (M' + 1) (M'' + 1) ρ τ (p + 1)
            + innerSwapFour X k (genB X k i M' M'' ρ τ p))
          + genFL X k (i + 1) M' M'' ρ τ (p + 1) := by
    intro p _
    show padFourL X k (M' + 1 + (p + 1)) (M'' + 1 + (i + 1 - (p + 1)))
          (phiAtDeg X (M' + 1 + (p + 1)) (p + 1) ρ)
          ((groupRingGen ^ (p + 1)) •
            phiAtDeg X (M'' + 1 + (i + 1 - (p + 1))) (i + 1 - (p + 1)) τ)
        = (cancelA X k i (M' + 1) (M'' + 1) ρ τ (p + 1)
            + innerSwapFour X k (genB X k i M' M'' ρ τ p))
          + faceLAt X k (M'' + 1 + (i + 1 - (p + 1))) (p + 1) (i + 1 - (p + 1)) M' ρ τ
              (M' + (p + 1))
    rw [padFourL_back_congr X k (M' + 1 + (p + 1)) (p + 1) ρ τ (Nat.succ_sub_succ i p),
      faceLAt_back_congr X k (p + 1) M' (M' + (p + 1)) ρ τ (Nat.succ_sub_succ i p),
      faceLAt_congr X k (M'' + 1 + (i - p)) (p + 1) (i - p) M' ρ τ
        (show M' + (p + 1) = M' + 1 + p by omega)]
    exact bTerm_left_split X k M' p (M'' + 1 + (i - p)) (i - p) ρ τ
  -- the right block below the top index, in three pieces
  have hRs : ∀ p ∈ Finset.range (i + 1),
      genR X k (i + 1) M' M'' ρ τ p
        = (genB X k i M' M'' ρ τ p + cancelB X k i (M' + 1) (M'' + 1) ρ τ p)
          + genFR X k (i + 1) M' M'' ρ τ p := by
    intro p hp
    have hp' : p < i + 1 := Finset.mem_range.mp hp
    show padFourR X k (M' + 1 + p) (M'' + 1 + (i + 1 - p)) (phiAtDeg X (M' + 1 + p) p ρ)
          ((groupRingGen ^ p) • phiAtDeg X (M'' + 1 + (i + 1 - p)) (i + 1 - p) τ)
        = (genB X k i M' M'' ρ τ p + cancelB X k i (M' + 1) (M'' + 1) ρ τ p)
          + faceRAt X k (M' + 1 + p) p (i + 1 - p) M'' ρ τ (M'' + (i + 1 - p))
    rw [padFourR_back_congr X k (M' + 1 + p) p ρ τ (show i + 1 - p = i - p + 1 by omega),
      faceRAt_back_congr X k (M' + 1 + p) p M'' ρ τ
        (show i + 1 - p = i - p + 1 by omega),
      faceRAt_congr X k (M' + 1 + p) p (i - p + 1) M'' ρ τ
        (show M'' + (i - p + 1) = M'' + 1 + (i - p) by omega)]
    exact bTerm_right_split X k (M' + 1 + p) M'' (i - p) p ρ τ
  -- the right block at the top index has no boundary to take but the faces
  have hRt : genR X k (i + 1) M' M'' ρ τ (i + 1) = genFR X k (i + 1) M' M'' ρ τ (i + 1) := by
    show padFourR X k (M' + 1 + (i + 1)) (M'' + 1 + (i + 1 - (i + 1)))
          (phiAtDeg X (M' + 1 + (i + 1)) (i + 1) ρ)
          ((groupRingGen ^ (i + 1)) •
            phiAtDeg X (M'' + 1 + (i + 1 - (i + 1))) (i + 1 - (i + 1)) τ)
        = faceRAt X k (M' + 1 + (i + 1)) (i + 1) (i + 1 - (i + 1)) M'' ρ τ
            (M'' + (i + 1 - (i + 1)))
    rw [padFourR_back_congr X k (M' + 1 + (i + 1)) (i + 1) ρ τ (Nat.sub_self (i + 1)),
      faceRAt_back_congr X k (M' + 1 + (i + 1)) (i + 1) M'' ρ τ (Nat.sub_self (i + 1))]
    exact padFourR_compBPre_zero X k (M' + 1 + (i + 1)) M'' (i + 1) _ τ
  -- the two block sums
  have hLsum : (∑ p ∈ Finset.range (i + 1 + 1), genL X k (i + 1) M' M'' ρ τ p)
      = ((∑ p ∈ Finset.range (i + 1 + 1), cancelA X k i (M' + 1) (M'' + 1) ρ τ p)
          + innerSwapFour X k (∑ p ∈ Finset.range (i + 1), genB X k i M' M'' ρ τ p))
        + ∑ p ∈ Finset.range (i + 1 + 1), genFL X k (i + 1) M' M'' ρ τ p := by
    rw [Finset.sum_range_succ' (genL X k (i + 1) M' M'' ρ τ) (i + 1),
      Finset.sum_congr rfl hLs, hL0, Finset.sum_add_distrib, Finset.sum_add_distrib,
      Finset.sum_range_succ' (cancelA X k i (M' + 1) (M'' + 1) ρ τ) (i + 1),
      cancelA_zero, Finset.sum_range_succ' (genFL X k (i + 1) M' M'' ρ τ) (i + 1),
      map_sum (innerSwapFour X k)]
    abel
  have hRsum : (∑ p ∈ Finset.range (i + 1 + 1), genR X k (i + 1) M' M'' ρ τ p)
      = ((∑ p ∈ Finset.range (i + 1), genB X k i M' M'' ρ τ p)
          + ∑ p ∈ Finset.range (i + 1), cancelB X k i (M' + 1) (M'' + 1) ρ τ p)
        + ∑ p ∈ Finset.range (i + 1 + 1), genFR X k (i + 1) M' M'' ρ τ p := by
    rw [Finset.sum_range_succ (genR X k (i + 1) M' M'' ρ τ) (i + 1),
      Finset.sum_congr rfl hRs, hRt, Finset.sum_add_distrib, Finset.sum_add_distrib,
      Finset.sum_range_succ (genFR X k (i + 1) M' M'' ρ τ) (i + 1)]
    abel
  -- the cancellation, and the regrouping that exposes it
  have hcan := sum_cancelA_cancelB X k i (M' + 1) (M'' + 1) (i + 1) ρ τ
  have hshuffle : ∀ A B C D E F : (TensorIdx (pairFreeCx X) (pairFreeCx X) k →₀ ZMod 2),
      ((A + B) + C) + ((D + E) + F) = (A + E) + ((D + B) + (C + F)) :=
    fun A B C D E F => by abel
  rw [hsplit, hLsum, hRsum, hshuffle, hcan, zero_add]

end

end Steenrod
end CharClass
end GroupApproximation
