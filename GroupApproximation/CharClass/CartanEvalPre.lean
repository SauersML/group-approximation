import GroupApproximation.CharClass.CartanEvalPhiAtDeg
import GroupApproximation.CharClass.CartanMidFourChainMap
import GroupApproximation.CharClass.SteenrodFourfoldB

/-!
# The functional seen before the interchange

Composite B is the interchange of a pre-interchange value, so evaluating it means
evaluating a different functional on that value.  The interchange sends the two
first factors to the new first block and the two second factors to the new
second, so the functional that takes `α, β, α, β` across the four slots of the
interchanged element takes `α, α, β, β` across the four slots of the original.

That is exactly the slot convention that makes the answer a product of two
squares rather than a cross term: each cochain meets both factors of one
diagonal value.  The proof is `ring` on four commuting factors.

## Main results

* `fourEvalPre` — the functional before the interchange.
* `fourEvalF2_midSwap` — the two are the same functional across the interchange.
* `fourEvalPre_padFour_of_eq` — it factors as two pair pairings.
* `pairEvalIdx_pow_smul` — the resolution's power of the generator is invisible
  to a pairing whose two cochains are equal.
-/

open CategoryTheory
open GroupApproximation.ThirdParty.HamSandwich.SphereOddDegree

namespace GroupApproximation.CharClass

noncomputable section

/-! ## 1. The functional before the interchange -/

/-- The value on a basis element: the first cochain against both factors of the
first block, the second against both factors of the second. -/
noncomputable def fourEvalPreGen (X : TopCat.{0}) (p q : ℕ)
    (α : singularCochainGroup (ZMod 2) X p) (β : singularCochainGroup (ZMod 2) X q)
    {k : ℕ} (Z : TensorIdx (pairFreeCx X) (pairFreeCx X) k) : ZMod 2 :=
  evAt X p α Z.2.1.1.val.1 Z.2.1.2.1 * evAt X p α Z.2.1.1.val.2 Z.2.1.2.2
    * (evAt X q β Z.2.2.1.val.1 Z.2.2.2.1 * evAt X q β Z.2.2.1.val.2 Z.2.2.2.2)

noncomputable def fourEvalPre (X : TopCat.{0}) (p q : ℕ)
    (α : singularCochainGroup (ZMod 2) X p) (β : singularCochainGroup (ZMod 2) X q)
    (k : ℕ) :
    (TensorIdx (pairFreeCx X) (pairFreeCx X) k →₀ ZMod 2) →ₗ[ZMod 2] ZMod 2 :=
  Finsupp.linearCombination (ZMod 2) (fourEvalPreGen X p q α β)

@[simp] theorem fourEvalPre_single (X : TopCat.{0}) (p q : ℕ)
    (α : singularCochainGroup (ZMod 2) X p) (β : singularCochainGroup (ZMod 2) X q)
    (k : ℕ) (Z : TensorIdx (pairFreeCx X) (pairFreeCx X) k) (c : ZMod 2) :
    fourEvalPre X p q α β k (Finsupp.single Z c) = c * fourEvalPreGen X p q α β Z := by
  unfold fourEvalPre
  rw [Finsupp.linearCombination_single, smul_eq_mul]

/-! ## 2. The two functionals across the interchange -/

/-- **The slot convention.**  The interchange carries the `α, β, α, β` functional
to the `α, α, β, β` one, so each cochain meets both factors of one diagonal
value. -/
theorem fourEvalGen_midIdx (X : TopCat.{0}) (p q : ℕ)
    (α : singularCochainGroup (ZMod 2) X p) (β : singularCochainGroup (ZMod 2) X q)
    {k : ℕ} (Z : TensorIdx (pairFreeCx X) (pairFreeCx X) k) :
    fourEvalGen X p q α β
        (midIdx (singFreeCx X) (singFreeCx X) (singFreeCx X) (singFreeCx X) Z)
      = fourEvalPreGen X p q α β Z := by
  show evAt X p α Z.2.1.1.val.1 Z.2.1.2.1 * evAt X q β Z.2.2.1.val.1 Z.2.2.2.1
      * (evAt X p α Z.2.1.1.val.2 Z.2.1.2.2 * evAt X q β Z.2.2.1.val.2 Z.2.2.2.2)
    = evAt X p α Z.2.1.1.val.1 Z.2.1.2.1 * evAt X p α Z.2.1.1.val.2 Z.2.1.2.2
      * (evAt X q β Z.2.2.1.val.1 Z.2.2.2.1 * evAt X q β Z.2.2.1.val.2 Z.2.2.2.2)
  ring

theorem fourEvalF2_midSwap (X : TopCat.{0}) (p q : ℕ)
    (α : singularCochainGroup (ZMod 2) X p) (β : singularCochainGroup (ZMod 2) X q)
    (k : ℕ) (y : TensorIdx (pairFreeCx X) (pairFreeCx X) k →₀ ZMod 2) :
    fourEvalF2 X p q α β k
        (midSwap (singFreeCx X) (singFreeCx X) (singFreeCx X) (singFreeCx X) k y)
      = fourEvalPre X p q α β k y := by
  induction y using Finsupp.induction_linear with
  | zero => rw [map_zero, map_zero, map_zero]
  | add u v hu hv => rw [map_add, map_add, map_add, hu, hv]
  | single Z c =>
      rw [midSwap_single, fourEvalF2_single, fourEvalPre_single, fourEvalGen_midIdx]

/-! ## 3. The factorisation -/

theorem fourEvalPre_tenElt_single_single (X : TopCat.{0}) (p q : ℕ)
    (α : singularCochainGroup (ZMod 2) X p) (β : singularCochainGroup (ZMod 2) X q)
    (k a b : ℕ) (h : a + b = k)
    (u : Steenrod.PairIdx X a) (v : Steenrod.PairIdx X b) :
    fourEvalPre X p q α β k
        (tenElt (pairFreeCx X) (pairFreeCx X) (⟨(a, b), h⟩ : Steenrod.PairDeg k)
          (Finsupp.single u 1) (Finsupp.single v 1))
      = pairEvalGen X p p α α a u * pairEvalGen X q q β β b v := by
  rw [tenElt_single_single, fourEvalPre_single, one_mul]
  rfl

theorem fourEvalPre_tenElt_pair (X : TopCat.{0}) (p q : ℕ)
    (α : singularCochainGroup (ZMod 2) X p) (β : singularCochainGroup (ZMod 2) X q)
    (k a b : ℕ) (h : a + b = k)
    (U : Steenrod.PairIdx X a →₀ ZMod 2) (V : Steenrod.PairIdx X b →₀ ZMod 2) :
    fourEvalPre X p q α β k
        (tenElt (pairFreeCx X) (pairFreeCx X) (⟨(a, b), h⟩ : Steenrod.PairDeg k) U V)
      = pairEvalIdx X p p α α a U * pairEvalIdx X q q β β b V := by
  induction U using Finsupp.induction_linear with
  | zero => rw [tenElt_zero_left, map_zero, map_zero, zero_mul]
  | add u1 u2 h1 h2 => rw [tenElt_add_left, map_add, h1, h2, map_add, add_mul]
  | single u c =>
      induction V using Finsupp.induction_linear with
      | zero => rw [tenElt_zero_right, map_zero, map_zero, mul_zero]
      | add v1 v2 g1 g2 => rw [tenElt_add_right, map_add, g1, g2, map_add, mul_add]
      | single v d =>
          rw [pairEvalIdx_single, pairEvalIdx_single,
            show (Finsupp.single u c : Steenrod.PairIdx X a →₀ ZMod 2)
                = c • Finsupp.single u (1 : ZMod 2) by
              rw [Finsupp.smul_single, smul_eq_mul, mul_one],
            show (Finsupp.single v d : Steenrod.PairIdx X b →₀ ZMod 2)
                = d • Finsupp.single v (1 : ZMod 2) by
              rw [Finsupp.smul_single, smul_eq_mul, mul_one],
            tenElt_smul_left, tenElt_smul_right, map_smul, map_smul, smul_eq_mul,
            smul_eq_mul, fourEvalPre_tenElt_single_single]
          ring

theorem fourEvalPre_padFour_of_eq (X : TopCat.{0}) (p q : ℕ)
    (α : singularCochainGroup (ZMod 2) X p) (β : singularCochainGroup (ZMod 2) X q)
    (k a b : ℕ) (h : a + b = k)
    (U : Steenrod.PairIdx X a →₀ ZMod 2) (V : Steenrod.PairIdx X b →₀ ZMod 2) :
    fourEvalPre X p q α β k (Steenrod.padFour X k a b U V)
      = pairEvalIdx X p p α α a U * pairEvalIdx X q q β β b V := by
  rw [Steenrod.padFour_of_eq h, fourEvalPre_tenElt_pair X p q α β k a b h U V]

theorem fourEvalPre_padFour_of_ne (X : TopCat.{0}) (p q : ℕ)
    (α : singularCochainGroup (ZMod 2) X p) (β : singularCochainGroup (ZMod 2) X q)
    (k a b : ℕ) (h : ¬ a + b = k)
    (U : Steenrod.PairIdx X a →₀ ZMod 2) (V : Steenrod.PairIdx X b →₀ ZMod 2) :
    fourEvalPre X p q α β k (Steenrod.padFour X k a b U V) = 0 := by
  rw [Steenrod.padFour_of_ne h, map_zero]

/-! ## 4. The resolution's generator is invisible -/

/-- A pairing whose two cochains are equal is invariant under the factor swap. -/
theorem pairEvalIdx_swapEnd (X : TopCat.{0}) (m b : ℕ)
    (γ : singularCochainGroup (ZMod 2) X m) (V : Steenrod.PairIdx X b →₀ ZMod 2) :
    pairEvalIdx X m m γ γ b (Steenrod.swapEnd X b V) = pairEvalIdx X m m γ γ b V := by
  induction V using Finsupp.induction_linear with
  | zero => rw [map_zero, map_zero]
  | add u v hu hv => rw [map_add, map_add, map_add, hu, hv]
  | single u c =>
      rw [Steenrod.swapEnd_single, pairEvalIdx_single, pairEvalIdx_single]
      show c * (evAt X m γ u.1.val.2 u.2.2 * evAt X m γ u.1.val.1 u.2.1)
        = c * (evAt X m γ u.1.val.1 u.2.1 * evAt X m γ u.1.val.2 u.2.2)
      ring

/-- **The power of the generator is invisible** to such a pairing. -/
theorem pairEvalIdx_pow_smul (X : TopCat.{0}) (m b : ℕ)
    (γ : singularCochainGroup (ZMod 2) X m) (j : ℕ)
    (V : Steenrod.PairIdx X b →₀ ZMod 2) :
    pairEvalIdx X m m γ γ b ((groupRingGen ^ j : GroupRingZ2) • V)
      = pairEvalIdx X m m γ γ b V := by
  induction j generalizing V with
  | zero => rw [pow_zero, one_smul]
  | succ j ih =>
      rw [pow_succ, mul_smul, ih, Steenrod.groupRingGen_smul, pairEvalIdx_swapEnd]

end

end GroupApproximation.CharClass
