import GroupApproximation.CharClass.SteenrodFourfoldAW
import GroupApproximation.CharClass.CartanFourfold

/-!
# The first composite, `A = (Φ₀ ⊗ Φ₀) ∘ Φ`

The comparison of the Cartan formula compares two natural equivariant chain maps
`W ⊗ S(X) → S(X)^{⊗4}`.  This file builds the first, and almost all of it is
assembly: `Φ` is already a natural equivariant chain map, `Φ₀` is already a chain
map, and `cc-cartan`'s `FreeCxHom` machinery already tensors two chain maps into
one and knows that the result commutes with the swap.

So the only new content is the observation that `Φ₀` is a `FreeCxHom` at all,
which needs the two identifications `(singFreeCx X).d = ∂` and
`(pairFreeCx X).d = dTgt`, both definitional or already proved.

## Why the action is the block swap

`Λ` acts on the fourfold by `tenSwap (pairFreeCx X)`, which exchanges the two
*blocks*.  On the four underlying tensor factors that is the permutation
`(13)(24)`, which is the one the comparison needs: `A` intertwines the generator
with it because `Φ` intertwines the generator with the swap of `Φ`'s two outputs,
and `Φ₀ ⊗ Φ₀` carries that swap to the block swap.  Nothing here would work with
`(12)(34)`.

## Main results

* `awHom`, `awPairHom` — `Φ₀` and `Φ₀ ⊗ Φ₀` as chain maps.
* `compA` — **the first composite**, `Λ`-linear.
* `tensorD_compA` — it is a chain map.
* `compA_zero` — it sends `e₀ ⊗ x` to `x ⊗ x ⊗ x ⊗ x`.
-/

open CategoryTheory
open GroupApproximation.ThirdParty.HamSandwich.SphereOddDegree

namespace GroupApproximation
namespace CharClass
namespace Steenrod

noncomputable section

/-! ## 1. `Φ₀` and `Φ₀ ⊗ Φ₀` as chain maps -/

/-- **The Alexander–Whitney diagonal as a chain map** `S(X) → S(X) ⊗ S(X)`. -/
noncomputable def awHom (X : TopCat.{0}) : FreeCxHom (singFreeCx X) (pairFreeCx X) where
  f k := awDiag X k
  comm k u := by
    show awDiag X k (bdU (ZMod 2) X k u)
        = tensorD (singFreeCx X) (singFreeCx X) k (awDiag X (k + 1) u)
    rw [tensorD_eq_dTgt]
    exact (dTgt_awDiag X k u).symm

/-- `Φ₀ ⊗ Φ₀`, from the pair complex to the fourfold. -/
noncomputable def awPairHom (X : TopCat.{0}) : FreeCxHom (pairFreeCx X) (fourFreeCx X) :=
  tenFreeCxHom (awHom X) (awHom X)

/-- `Φ₀ ⊗ Φ₀` carries the factor swap of the pair to the **block** swap of the
fourfold.  This is where `(13)(24)` rather than `(12)(34)` comes from. -/
theorem awPairHom_swap (X : TopCat.{0}) (k : ℕ) (z : PairIdx X k →₀ ZMod 2) :
    (awPairHom X).f k (swapEnd X k z)
      = tenSwap (pairFreeCx X) k ((awPairHom X).f k z) :=
  tenHom_tenSwap (awHom X) k z

theorem awPairHom_smul (X : TopCat.{0}) (k : ℕ) (c : GroupRingZ2)
    (z : PairIdx X k →₀ ZMod 2) :
    (awPairHom X).f k (c • z) = c • (awPairHom X).f k z :=
  galAlgHom_comm (swapEnd X k) (swapEnd_sq X k)
    (tenSwap (pairFreeCx X) k) (tenSwap_mul_self (pairFreeCx X) k)
    ((awPairHom X).f k) (awPairHom_swap X k) c z

/-- `Φ₀ ⊗ Φ₀` as a map of modules over the group ring. -/
noncomputable def awPairLambda (X : TopCat.{0}) (k : ℕ) :
    (PairIdx X k →₀ ZMod 2) →ₗ[GroupRingZ2]
      (TensorIdx (pairFreeCx X) (pairFreeCx X) k →₀ ZMod 2) where
  toFun := (awPairHom X).f k
  map_add' u v := map_add _ u v
  map_smul' c z := awPairHom_smul X k c z

/-! ## 2. The composite -/

/-- **The first composite of the Cartan comparison**, `(Φ₀ ⊗ Φ₀) ∘ Φ`, as a map
of modules over the group ring. -/
noncomputable def compA (X : TopCat.{0}) (k : ℕ) :
    WTensorSMod X k →ₗ[GroupRingZ2]
      (TensorIdx (pairFreeCx X) (pairFreeCx X) k →₀ ZMod 2) :=
  (awPairLambda X k).comp (PhiHom X k)

@[simp] theorem compA_apply (X : TopCat.{0}) (k : ℕ) (y : WTensorSMod X k) :
    compA X k y = (awPairHom X).f k (PhiHom X k y) := rfl

/-- **The first composite is a chain map.** -/
theorem tensorD_compA (X : TopCat.{0}) (k : ℕ) (y : WTensorSMod X (k + 1)) :
    tensorD (pairFreeCx X) (pairFreeCx X) k (compA X (k + 1) y)
      = compA X k (wDiff singularBoundary X k y) :=
  calc tensorD (pairFreeCx X) (pairFreeCx X) k
        ((awPairHom X).f (k + 1) (PhiHom X (k + 1) y))
      = (awPairHom X).f k (tensorD (singFreeCx X) (singFreeCx X) k (PhiHom X (k + 1) y)) :=
        ((awPairHom X).comm k (PhiHom X (k + 1) y)).symm
    _ = (awPairHom X).f k (dTgt X (ZMod 2) k (PhiHom X (k + 1) y)) :=
        congrArg ((awPairHom X).f k) (tensorD_eq_dTgt X k _)
    _ = (awPairHom X).f k (PhiHom X k (wDiff singularBoundary X k y)) :=
        congrArg ((awPairHom X).f k) (dTgt_PhiHom X k y)

/-! ## 3. The degree-zero value -/

/-- `x ⊗ x ⊗ x ⊗ x`, written as `Φ₀(x) ⊗ Φ₀(x)`: the value both composites take
on `e₀ ⊗ x`, and the reason the acyclic-models uniqueness applies to them. -/
def fourDiagZero (X : TopCat.{0}) (σ : singularSimplices X 0) :
    TensorIdx (pairFreeCx X) (pairFreeCx X) 0 →₀ ZMod 2 :=
  tenElt (pairFreeCx X) (pairFreeCx X) (⟨(0, 0), rfl⟩ : PairDeg 0)
    (phiZero X 0 σ) (phiZero X 0 σ)

theorem awPairHom_phiZero_zero (X : TopCat.{0}) (σ : singularSimplices X 0) :
    (awPairHom X).f 0 (phiZero X 0 σ) = fourDiagZero X σ := by
  rw [phiZero_degree_zero]
  show tenHom (awHom X) (awHom X) 0
      (Finsupp.single (⟨⟨(0, 0), rfl⟩, (σ, σ)⟩ : PairIdx X 0) 1) = _
  rw [tenHom_single, one_smul]
  show tenElt (pairFreeCx X) (pairFreeCx X) (⟨(0, 0), rfl⟩ : PairDeg 0)
      (awDiag X 0 (Finsupp.single σ 1)) (awDiag X 0 (Finsupp.single σ 1)) = _
  rw [awDiag_single_one]
  rfl

/-- **The degree-zero normalisation.**  `A(e₀ ⊗ x) = x ⊗ x ⊗ x ⊗ x`. -/
theorem compA_zero (X : TopCat.{0})
    (φ : stdSimplexTop (0 : Fin (0 + 1)).val ⟶ X) :
    compA X 0 (Finsupp.single (⟨0, φ⟩ : Σ n : Fin (0 + 1), stdSimplexTop n.val ⟶ X) 1)
      = fourDiagZero X ((simplexEquiv X 0).symm φ) := by
  show (awPairHom X).f 0 (PhiHom X 0 (Finsupp.single (⟨0, φ⟩ : Σ n : Fin (0 + 1), stdSimplexTop n.val ⟶ X) 1)) = _
  rw [PhiHom_single, one_smul]
  have hz : phiPair X 0 (wsOfHom X 0 ⟨0, φ⟩)
      = phiZero X 0 ((simplexEquiv X 0).symm φ) := phiPair_last X 0 _
  rw [hz]
  exact awPairHom_phiZero_zero X _

/-! ## 4. Naturality -/

theorem singHom_single {X Y : TopCat.{0}} (f : X ⟶ Y) (a : ℕ)
    (x : singularSimplices X a) :
    (singHom f).f a (Finsupp.single x (1 : ZMod 2))
      = Finsupp.single (pushSimplex f a x) 1 := by
  show Finsupp.mapDomain (pushSimplex f a) (Finsupp.single x (1 : ZMod 2)) = _
  exact Finsupp.mapDomain_single

/-- The pushforward on the pair complex, in this lane's vocabulary.  The two
presentations agree because a decomposable of two singles is a single.

`singFreeCx` is a plain `def`, so `rw` with a lemma whose left side mentions
`A.ι` cannot see that the index type is a type of simplices; everything below is
therefore `calc` closed by `exact`, and the only rewrites are with closed
equations. -/
theorem pairHom_f_eq {X Y : TopCat.{0}} (f : X ⟶ Y) (k : ℕ) :
    (pairHom f).f k = pairPushLin X Y f k := by
  apply Finsupp.lhom_ext'
  intro q
  apply LinearMap.ext_ring
  obtain ⟨⟨⟨a, b⟩, hab⟩, x, y⟩ := q
  show (pairHom f).f k
      (Finsupp.single (⟨⟨(a, b), hab⟩, (x, y)⟩ : PairIdx X k) (1 : ZMod 2))
    = pairPushLin X Y f k
      (Finsupp.single (⟨⟨(a, b), hab⟩, (x, y)⟩ : PairIdx X k) (1 : ZMod 2))
  calc (pairHom f).f k
        (Finsupp.single (⟨⟨(a, b), hab⟩, (x, y)⟩ : PairIdx X k) (1 : ZMod 2))
      = tenElt (singFreeCx Y) (singFreeCx Y) (⟨(a, b), hab⟩ : PairDeg k)
          ((singHom f).f a (Finsupp.single x 1))
          ((singHom f).f b (Finsupp.single y 1)) :=
        (tenHom_single (singHom f) (singHom f) k
          (⟨⟨(a, b), hab⟩, (x, y)⟩ : PairIdx X k) 1).trans (one_smul _ _)
    _ = tenElt (singFreeCx Y) (singFreeCx Y) (⟨(a, b), hab⟩ : PairDeg k)
          (Finsupp.single (pushSimplex f a x) 1)
          (Finsupp.single (pushSimplex f b y) 1) := by
        have hx := singHom_single f a x
        have hy := singHom_single f b y
        rw [hx, hy]
        rfl
    _ = Finsupp.single
          (⟨⟨(a, b), hab⟩, (pushSimplex f a x, pushSimplex f b y)⟩ : PairIdx Y k) 1 :=
        tenElt_single_single (singFreeCx Y) (singFreeCx Y) _ _ _
    _ = pairPushLin X Y f k
          (Finsupp.single (⟨⟨(a, b), hab⟩, (x, y)⟩ : PairIdx X k) 1) :=
        (pairPushLin_single f k (⟨⟨(a, b), hab⟩, (x, y)⟩ : PairIdx X k) 1).symm

theorem pairPushLin_awDiag {X Y : TopCat.{0}} (f : X ⟶ Y) (m : ℕ)
    (u : singularSimplices X m →₀ ZMod 2) :
    pairPushLin X Y f m (awDiag X m u)
      = awDiag Y m (Finsupp.mapDomain (pushSimplex f m) u) := by
  induction u using Finsupp.induction_linear with
  | zero => simp
  | add p q hp hq =>
      rw [map_add (awDiag X m), map_add (pairPushLin X Y f m), hp, hq,
        Finsupp.mapDomain_add, map_add (awDiag Y m)]
  | single σ c =>
      rw [awDiag_single, map_smul, phiZero_naturality, Finsupp.mapDomain_single,
        awDiag_single]

/-- `Φ₀` is natural, as an equation of chain maps. -/
theorem awHom_natural {X Y : TopCat.{0}} (f : X ⟶ Y) :
    (pairHom f).comp (awHom X) = (awHom Y).comp (singHom f) := by
  refine FreeCxHom.ext (funext fun m => ?_)
  apply LinearMap.ext
  intro u
  show (pairHom f).f m (awDiag X m u) = awDiag Y m ((singHom f).f m u)
  rw [pairHom_f_eq]
  show pairPushLin X Y f m (awDiag X m u)
      = awDiag Y m (Finsupp.mapDomain (pushSimplex f m) u)
  exact pairPushLin_awDiag f m u

theorem awPairHom_natural {X Y : TopCat.{0}} (f : X ⟶ Y) (k : ℕ)
    (z : PairIdx X k →₀ ZMod 2) :
    (fourHom f).f k ((awPairHom X).f k z) = (awPairHom Y).f k ((pairHom f).f k z) := by
  show tenHom (pairHom f) (pairHom f) k (tenHom (awHom X) (awHom X) k z)
      = tenHom (awHom Y) (awHom Y) k (tenHom (singHom f) (singHom f) k z)
  rw [← tenHom_comp, ← tenHom_comp, awHom_natural]

/-- **The first composite is natural in the space.** -/
theorem fourHom_compA {X Y : TopCat.{0}} (f : X ⟶ Y) (k : ℕ) (y : WTensorSMod X k) :
    (fourHom f).f k (compA X k y)
      = compA Y k (Finsupp.lmapDomain GroupRingZ2 GroupRingZ2 (srcMapIdx f k) y) := by
  have h2 : (pairHom f).f k (PhiHom X k y)
      = PhiHom Y k (Finsupp.lmapDomain GroupRingZ2 GroupRingZ2 (srcMapIdx f k) y) := by
    rw [pairHom_f_eq]
    exact PhiHom_naturality f k y
  show (fourHom f).f k ((awPairHom X).f k (PhiHom X k y)) = _
  rw [awPairHom_natural, h2]
  rfl

end

end Steenrod
end CharClass
end GroupApproximation
