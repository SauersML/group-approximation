import GroupApproximation.CharClass.CartanTargetSwap

/-!
# The pair differential commutes with the factor swap

`CartanTargetSwap.lean` puts the group ring on `S(X) ⊗ S(X)` through the factor
swap `T`.  For that action to make `cc-steenrod`'s differential `dTgt` a map of
`Λ`-modules — which is what the acyclic-models comparison needs — the
differential has to commute with `T`.  It does, and for the reason the reader
expects: `dTgt` is the sum of the two per-factor halves `dLeft` and `dRight`,
and the swap exchanges them.

The exchange is exact, not merely up to sign, because we are in characteristic
two: `dGen` carries no alternating signs, so `T ∘ dLeft = dRight ∘ T` on the
nose.

## Main results

* `dLeft_swap`, `dRight_swap` — each half of the differential turns into the
  other one under the swap.
* `dGen_pairIdxSwap` — the swap intertwines the differential on a basis element.
* `dTgt_pairSwap` — **the differential is `T`-equivariant**, and so `Λ`-linear
  for `pairModule`.
* `dTgt_smul` — the `Λ`-linearity itself, stated for an arbitrary scalar.
-/

namespace GroupApproximation.CharClass

open CategoryTheory
open GroupApproximation.ThirdParty.HamSandwich.SphereOddDegree
open GroupApproximation.ThirdParty.HamSandwich.SphereOddDegree.AlexanderWhitney

noncomputable section

/-! ## 1. The two halves change places -/

/-- `∂ ⊗ 1` on the swapped pair is the swap of `1 ⊗ ∂` on the original.  Both
boundary proofs are arguments, so no cast is ever formed. -/
theorem dLeft_swap (X : TopCat.{0}) (k a b : ℕ)
    (h : b + a = k + 1) (h' : a + b = k + 1)
    (σ : singularSimplices X a) (τ : singularSimplices X b) :
    Steenrod.dLeft X (ZMod 2) k b a h τ σ
      = pairSwap X k (Steenrod.dRight X (ZMod 2) k a b h' σ τ) := by
  cases b with
  | zero => rw [Steenrod.dLeft_zero, Steenrod.dRight_zero, map_zero]
  | succ b' =>
      rw [Steenrod.dLeft_succ, Steenrod.dRight_succ]
      refine Eq.trans ?_ (map_sum (pairSwap X k) _ Finset.univ).symm
      refine Finset.sum_congr rfl fun j _ => ?_
      symm
      exact pairSwap_single X k _ 1

/-- `1 ⊗ ∂` on the swapped pair is the swap of `∂ ⊗ 1` on the original. -/
theorem dRight_swap (X : TopCat.{0}) (k a b : ℕ)
    (h : b + a = k + 1) (h' : a + b = k + 1)
    (σ : singularSimplices X a) (τ : singularSimplices X b) :
    Steenrod.dRight X (ZMod 2) k b a h τ σ
      = pairSwap X k (Steenrod.dLeft X (ZMod 2) k a b h' σ τ) := by
  cases a with
  | zero => rw [Steenrod.dRight_zero, Steenrod.dLeft_zero, map_zero]
  | succ a' =>
      rw [Steenrod.dRight_succ, Steenrod.dLeft_succ]
      refine Eq.trans ?_ (map_sum (pairSwap X k) _ Finset.univ).symm
      refine Finset.sum_congr rfl fun j _ => ?_
      symm
      exact pairSwap_single X k _ 1

/-! ## 2. The differential is equivariant -/

/-- The swap intertwines the differential on a basis element. -/
theorem dGen_pairIdxSwap (X : TopCat.{0}) (k : ℕ) (q : Steenrod.PairIdx X (k + 1)) :
    Steenrod.dGen X (ZMod 2) k (pairIdxSwap q)
      = pairSwap X k (Steenrod.dGen X (ZMod 2) k q) := by
  obtain ⟨⟨⟨a, b⟩, hab⟩, σ, τ⟩ := q
  have key : Steenrod.dLeft X (ZMod 2) k b a (by omega) τ σ
        + Steenrod.dRight X (ZMod 2) k b a (by omega) τ σ
      = pairSwap X k (Steenrod.dLeft X (ZMod 2) k a b hab σ τ
        + Steenrod.dRight X (ZMod 2) k a b hab σ τ) := by
    rw [dLeft_swap X k a b (by omega) hab σ τ, dRight_swap X k a b (by omega) hab σ τ,
      map_add]
    exact add_comm _ _
  exact key

/-- **The pair differential is `T`-equivariant.** -/
theorem dTgt_pairSwap (X : TopCat.{0}) (k : ℕ)
    (y : Steenrod.PairIdx X (k + 1) →₀ ZMod 2) :
    Steenrod.dTgt X (ZMod 2) k (pairSwap X (k + 1) y)
      = pairSwap X k (Steenrod.dTgt X (ZMod 2) k y) := by
  induction y using Finsupp.induction_linear with
  | zero => rfl
  | add f g hf hg => rw [map_add, map_add, map_add, map_add, hf, hg]
  | single q c =>
      rw [pairSwap_single, Steenrod.dTgt_single, Steenrod.dTgt_single, map_smul,
        dGen_pairIdxSwap]

/-! ## 3. `Λ`-linearity -/

/-- **An `F₂`-linear map that commutes with the two involutions is `Λ`-linear.**
Stated at the level of the algebra map, so that it can be used before either
module instance is in scope. -/
theorem galAlgHom_comm {V W : Type} [AddCommGroup V] [Module (ZMod 2) V]
    [AddCommGroup W] [Module (ZMod 2) W]
    (σ : Module.End (ZMod 2) V) (hσ : σ * σ = 1)
    (τ : Module.End (ZMod 2) W) (hτ : τ * τ = 1)
    (f : V →ₗ[ZMod 2] W) (hf : ∀ v, f (σ v) = τ (f v)) (c : GroupRingZ2) (v : V) :
    f ((galAlgHom σ hσ c) v) = (galAlgHom τ hτ c) (f v) := by
  induction c using MonoidAlgebra.induction_on with
  | hM g =>
      have hV : (galAlgHom σ hσ) (MonoidAlgebra.of (ZMod 2) (Multiplicative (ZMod 2)) g)
          = galEnd σ hσ g := by
        unfold galAlgHom
        exact MonoidAlgebra.lift_of _ _
      have hW : (galAlgHom τ hτ) (MonoidAlgebra.of (ZMod 2) (Multiplicative (ZMod 2)) g)
          = galEnd τ hτ g := by
        unfold galAlgHom
        exact MonoidAlgebra.lift_of _ _
      rw [hV, hW]
      show f ((if Multiplicative.toAdd g = 0 then (1 : Module.End (ZMod 2) V) else σ) v)
        = (if Multiplicative.toAdd g = 0 then (1 : Module.End (ZMod 2) W) else τ) (f v)
      split_ifs with h
      · rfl
      · exact hf v
  | hadd c₁ c₂ h₁ h₂ =>
      rw [map_add, map_add, LinearMap.add_apply, LinearMap.add_apply, map_add, h₁, h₂]
  | hsmul r c h =>
      rw [map_smul, map_smul, LinearMap.smul_apply, LinearMap.smul_apply, map_smul, h]

/-- **The differential is `Λ`-linear** for the swap action of the group ring:
equivariance under the generator is its whole content. -/
theorem dTgt_smul (X : TopCat.{0}) (k : ℕ) (c : GroupRingZ2)
    (y : Steenrod.PairIdx X (k + 1) →₀ ZMod 2) :
    letI := pairModule X (k + 1)
    letI := pairModule X k
    Steenrod.dTgt X (ZMod 2) k (c • y) = c • Steenrod.dTgt X (ZMod 2) k y := by
  letI := pairModule X (k + 1)
  letI := pairModule X k
  exact galAlgHom_comm (pairSwap X (k + 1)) (pairSwap_mul_self X (k + 1))
    (pairSwap X k) (pairSwap_mul_self X k) (Steenrod.dTgt X (ZMod 2) k)
    (fun v => dTgt_pairSwap X k v) c y

end

end GroupApproximation.CharClass
