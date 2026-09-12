import GroupApproximation.CharClass.SteenrodPairCell

/-!
# The target differential is equivariant, and group-ring linear

`dTgt` was built as a `ZMod 2`-linear map, because that is all its definition
needs.  For it to be the differential of a complex of `Λ`-modules — which is what
the acyclic-models comparison consumes — it has to be linear over the group ring
acting through the geometric swap.  That is this file.

## Why it is true, and why it is short

`∂ ⊗ 1` and `1 ⊗ ∂` are exchanged by the factor swap: the swap of the boundary of
the left factor is the boundary of the right factor of the swap.  On a basis
element that is literally the same sum of basis elements written in the other
order, with no sign to worry about mod 2, so `swapEnd_dLeft` and `swapEnd_dRight`
are one `Finset.sum_congr` each and `swapEnd_dGen` is `add_comm`.

Linearity over the whole group ring then follows by `MonoidAlgebra.induction_on`
on the coefficient.  Only two of its three cases carry content, and the scalar
case is trivial because `ZMod 2` has two elements: it is `0` or `1`, so no
scalar-tower instance is needed.
-/

open CategoryTheory Limits AlgebraicTopology Simplicial SimplexCategory
open GroupApproximation.ThirdParty.HamSandwich.SphereOddDegree
open GroupApproximation.ThirdParty.HamSandwich.SphereOddDegree.AlexanderWhitney

namespace GroupApproximation
namespace CharClass
namespace Steenrod

noncomputable section

variable {X : TopCat.{0}}

/-! ## 1. The swap exchanges the two halves -/

theorem swapEnd_dLeft (X : TopCat.{0}) (k a b : ℕ) (h : a + b = k + 1) (h' : b + a = k + 1)
    (σ : singularSimplices X a) (τ : singularSimplices X b) :
    swapEnd X k (dLeft X (ZMod 2) k a b h σ τ) = dRight X (ZMod 2) k b a h' τ σ := by
  cases a with
  | zero =>
      rw [dLeft_zero, dRight_zero]
      exact map_zero (swapEnd X k)
  | succ a' =>
      rw [dLeft_succ, dRight_succ, map_sum]
      refine Finset.sum_congr rfl fun j _ => ?_
      exact swapEnd_single X k _ 1

theorem swapEnd_dRight (X : TopCat.{0}) (k a b : ℕ) (h : a + b = k + 1) (h' : b + a = k + 1)
    (σ : singularSimplices X a) (τ : singularSimplices X b) :
    swapEnd X k (dRight X (ZMod 2) k a b h σ τ) = dLeft X (ZMod 2) k b a h' τ σ := by
  cases b with
  | zero =>
      rw [dRight_zero, dLeft_zero]
      exact map_zero (swapEnd X k)
  | succ b' =>
      rw [dRight_succ, dLeft_succ, map_sum]
      refine Finset.sum_congr rfl fun j _ => ?_
      exact swapEnd_single X k _ 1

theorem swapEnd_dGen (X : TopCat.{0}) (k : ℕ) (q : PairIdx X (k + 1)) :
    swapEnd X k (dGen X (ZMod 2) k q) = dGen X (ZMod 2) k (swapIdx q) := by
  have hq : q.1.val.1 + q.1.val.2 = k + 1 := q.1.property
  have hswap : dGen X (ZMod 2) k (swapIdx q)
      = dLeft X (ZMod 2) k q.1.val.2 q.1.val.1 (by omega) q.2.2 q.2.1
        + dRight X (ZMod 2) k q.1.val.2 q.1.val.1 (by omega) q.2.2 q.2.1 := rfl
  rw [dGen_eq, hswap, map_add,
    swapEnd_dLeft X k q.1.val.1 q.1.val.2 q.1.property (by omega) q.2.1 q.2.2,
    swapEnd_dRight X k q.1.val.1 q.1.val.2 q.1.property (by omega) q.2.1 q.2.2]
  exact add_comm _ _

/-- **The target differential is equivariant.** -/
theorem swapEnd_dTgt (X : TopCat.{0}) (k : ℕ) (y : PairIdx X (k + 1) →₀ ZMod 2) :
    swapEnd X k (dTgt X (ZMod 2) k y) = dTgt X (ZMod 2) k (swapEnd X (k + 1) y) := by
  classical
  refine Finsupp.induction_linear y ?_ ?_ ?_
  · simp
  · intro u v hu hv
    rw [map_add, map_add, hu, hv, map_add, map_add]
  · intro q c
    rw [dTgt_single, map_smul, swapEnd_single, dTgt_single]
    exact congrArg (fun z => c • z) (swapEnd_dGen X k q)

/-! ## 2. Linearity over the group ring -/

/-- **The target differential is `Λ`-linear**, for the module structure in which
the generator acts by the geometric swap. -/
theorem dTgt_smul (X : TopCat.{0}) (k : ℕ) (c : GroupRingZ2)
    (y : PairIdx X (k + 1) →₀ ZMod 2) :
    dTgt X (ZMod 2) k (c • y) = c • dTgt X (ZMod 2) k y := by
  refine MonoidAlgebra.induction_on
    (p := fun c : GroupRingZ2 =>
      dTgt X (ZMod 2) k (c • y) = c • dTgt X (ZMod 2) k y) c ?_ ?_ ?_
  · intro m
    rcases zmod2_eq_zero_or_one (Multiplicative.toAdd m) with hm | hm
    · have hm1 : m = 1 := by
        show Multiplicative.ofAdd (Multiplicative.toAdd m) = Multiplicative.ofAdd (0 : ZMod 2)
        rw [hm]
      have hone : (MonoidAlgebra.of (ZMod 2) (Multiplicative (ZMod 2)) m : GroupRingZ2) = 1 := by
        rw [hm1, map_one]
      rw [hone, one_smul, one_smul]
    · have hm1 : m = Multiplicative.ofAdd (1 : ZMod 2) := by
        show Multiplicative.ofAdd (Multiplicative.toAdd m) = Multiplicative.ofAdd (1 : ZMod 2)
        rw [hm]
      have hgen : (MonoidAlgebra.of (ZMod 2) (Multiplicative (ZMod 2)) m : GroupRingZ2)
          = groupRingGen := by
        rw [hm1]
        rfl
      rw [hgen, groupRingGen_smul, groupRingGen_smul]
      exact (swapEnd_dTgt X k y).symm
  · intro c₁ c₂ h₁ h₂
    rw [add_smul, map_add, h₁, h₂, add_smul]
  · intro r c hc
    rcases zmod2_eq_zero_or_one r with hr | hr
    · rw [hr, zero_smul]
      simp
    · rw [hr, one_smul]
      exact hc

/-- **The target differential as a map of `Λ`-modules.**  This is the
differential of the target of the acyclic-models comparison. -/
noncomputable def dTgtLin (X : TopCat.{0}) (k : ℕ) :
    (PairIdx X (k + 1) →₀ ZMod 2) →ₗ[GroupRingZ2] (PairIdx X k →₀ ZMod 2) where
  toFun := dTgt X (ZMod 2) k
  map_add' u v := map_add (dTgt X (ZMod 2) k) u v
  map_smul' c y := dTgt_smul X k c y

@[simp] theorem dTgtLin_apply (X : TopCat.{0}) (k : ℕ) (y : PairIdx X (k + 1) →₀ ZMod 2) :
    dTgtLin X k y = dTgt X (ZMod 2) k y := rfl

end

end Steenrod
end CharClass
end GroupApproximation
