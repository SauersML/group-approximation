import GroupApproximation.CharClass.CartanFourfold
import GroupApproximation.CharClass.CartanEvaluation
import GroupApproximation.CharClass.SteenrodCochain

/-!
# The functional the Cartan comparison is evaluated against

The last step of the Cartan formula evaluates the two composites against the
functional

```text
x₁ ⊗ x₂ ⊗ x₃ ⊗ x₄  ↦  α(x₁) · β(x₂) · α(x₃) · β(x₄)
```

for two cochains `α` and `β`.  This file builds it and proves the property that
makes it usable: it is linear over the group ring.

That linearity is the whole reason the action on the fourfold has to be the block
swap `(13)(24)` and not `(12)(34)`.  Exchanging the two blocks sends the product
above to `α(x₃)β(x₄)α(x₁)β(x₂)`, which is the same product; exchanging inside each
block would send it to `β(x₂)α(x₁)β(x₄)α(x₃)`, which is also the same product, but
the composite that the comparison produces is only equivariant for one of the two,
and it is the block swap.  So the functional's invariance is what turns the
comparison into an equation between cochains.

A cochain has a fixed degree while the four degrees of a fourfold index vary, so
`evAt` extends a cochain to every degree by zero.  That keeps the functional
cast-free: no simplex is ever transported except inside `evAt` itself, where the
transport is along an equality of natural numbers.

## Main results

* `evAt` — a cochain evaluated at a simplex of arbitrary degree.
* `fourEvalF2` — the functional, `F₂`-linearly.
* `fourEvalF2_tenSwap` — **it is invariant under the block swap.**
* `fourEval_smul` — hence linear over the group ring, with the coefficients
  carrying the trivial action.
-/

namespace GroupApproximation.CharClass

open CategoryTheory
open GroupApproximation.ThirdParty.HamSandwich.SphereOddDegree

noncomputable section

/-! ## 1. A cochain at an arbitrary degree -/

/-- A cochain of degree `p`, evaluated at a simplex of any degree: the value when
the degrees agree, and zero otherwise. -/
noncomputable def evAt (X : TopCat.{0}) (p : ℕ)
    (α : singularCochainGroup (ZMod 2) X p) (m : ℕ) (σ : singularSimplices X m) :
    ZMod 2 :=
  if h : m = p then cochainEval p α (h ▸ σ) else 0

@[simp] theorem evAt_self (X : TopCat.{0}) (p : ℕ)
    (α : singularCochainGroup (ZMod 2) X p) (σ : singularSimplices X p) :
    evAt X p α p σ = cochainEval p α σ := by
  unfold evAt
  rw [dif_pos rfl]

theorem evAt_of_ne (X : TopCat.{0}) (p : ℕ)
    (α : singularCochainGroup (ZMod 2) X p) (m : ℕ) (h : m ≠ p)
    (σ : singularSimplices X m) : evAt X p α m σ = 0 := by
  unfold evAt
  rw [dif_neg h]

/-! ## 2. The functional -/

/-- The functional on a basis element of the fourfold. -/
noncomputable def fourEvalGen (X : TopCat.{0}) (p q : ℕ)
    (α : singularCochainGroup (ZMod 2) X p) (β : singularCochainGroup (ZMod 2) X q)
    {k : ℕ} (Z : TensorIdx (pairFreeCx X) (pairFreeCx X) k) : ZMod 2 :=
  evAt X p α Z.2.1.1.val.1 Z.2.1.2.1 * evAt X q β Z.2.1.1.val.2 Z.2.1.2.2
    * (evAt X p α Z.2.2.1.val.1 Z.2.2.2.1 * evAt X q β Z.2.2.1.val.2 Z.2.2.2.2)

/-- **The evaluating functional**, extended linearly. -/
noncomputable def fourEvalF2 (X : TopCat.{0}) (p q : ℕ)
    (α : singularCochainGroup (ZMod 2) X p) (β : singularCochainGroup (ZMod 2) X q)
    (k : ℕ) :
    (TensorIdx (pairFreeCx X) (pairFreeCx X) k →₀ ZMod 2) →ₗ[ZMod 2] ZMod 2 :=
  Finsupp.linearCombination (ZMod 2) (fourEvalGen X p q α β)

@[simp] theorem fourEvalF2_single (X : TopCat.{0}) (p q : ℕ)
    (α : singularCochainGroup (ZMod 2) X p) (β : singularCochainGroup (ZMod 2) X q)
    (k : ℕ) (Z : TensorIdx (pairFreeCx X) (pairFreeCx X) k) (c : ZMod 2) :
    fourEvalF2 X p q α β k (Finsupp.single Z c) = c * fourEvalGen X p q α β Z := by
  unfold fourEvalF2
  rw [Finsupp.linearCombination_single, smul_eq_mul]

/-! ## 3. Invariance under the block swap -/

theorem fourEvalGen_tenSwapIdx (X : TopCat.{0}) (p q : ℕ)
    (α : singularCochainGroup (ZMod 2) X p) (β : singularCochainGroup (ZMod 2) X q)
    {k : ℕ} (Z : TensorIdx (pairFreeCx X) (pairFreeCx X) k) :
    fourEvalGen X p q α β (tenSwapIdx (pairFreeCx X) Z) = fourEvalGen X p q α β Z := by
  show evAt X p α Z.2.2.1.val.1 Z.2.2.2.1 * evAt X q β Z.2.2.1.val.2 Z.2.2.2.2
      * (evAt X p α Z.2.1.1.val.1 Z.2.1.2.1 * evAt X q β Z.2.1.1.val.2 Z.2.1.2.2)
    = evAt X p α Z.2.1.1.val.1 Z.2.1.2.1 * evAt X q β Z.2.1.1.val.2 Z.2.1.2.2
      * (evAt X p α Z.2.2.1.val.1 Z.2.2.2.1 * evAt X q β Z.2.2.1.val.2 Z.2.2.2.2)
  ring

/-- **The functional is invariant under the block swap.**  This is what makes it
linear over the group ring, and it is the reason the action has to be `(13)(24)`. -/
theorem fourEvalF2_tenSwap (X : TopCat.{0}) (p q : ℕ)
    (α : singularCochainGroup (ZMod 2) X p) (β : singularCochainGroup (ZMod 2) X q)
    (k : ℕ) (y : TensorIdx (pairFreeCx X) (pairFreeCx X) k →₀ ZMod 2) :
    fourEvalF2 X p q α β k (tenSwap (pairFreeCx X) k y) = fourEvalF2 X p q α β k y := by
  induction y using Finsupp.induction_linear with
  | zero => rw [map_zero, map_zero]
  | add u v hu hv => rw [map_add, map_add, map_add, hu, hv]
  | single Z c =>
      rw [tenSwap_single, fourEvalF2_single, fourEvalF2_single,
        fourEvalGen_tenSwapIdx]

/-! ## 4. Linearity over the group ring -/

/-- **The functional is linear over the group ring**, with the coefficients
carrying the trivial action.  Immediate from the invariance, by the general
criterion of `CartanTargetEquivariance`. -/
theorem fourEval_galAlgHom (X : TopCat.{0}) (p q : ℕ)
    (α : singularCochainGroup (ZMod 2) X p) (β : singularCochainGroup (ZMod 2) X q)
    (k : ℕ) (c : GroupRingZ2)
    (y : TensorIdx (pairFreeCx X) (pairFreeCx X) k →₀ ZMod 2) :
    fourEvalF2 X p q α β k
        ((galAlgHom (tenSwap (pairFreeCx X) k) (tenSwap_mul_self (pairFreeCx X) k) c) y)
      = (galAlgHom (1 : Module.End (ZMod 2) (ZMod 2)) (one_mul 1) c)
          (fourEvalF2 X p q α β k y) :=
  galAlgHom_comm (tenSwap (pairFreeCx X) k) (tenSwap_mul_self (pairFreeCx X) k)
    (1 : Module.End (ZMod 2) (ZMod 2)) (one_mul 1) (fourEvalF2 X p q α β k)
    (fun v => fourEvalF2_tenSwap X p q α β k v) c y

end

end GroupApproximation.CharClass
