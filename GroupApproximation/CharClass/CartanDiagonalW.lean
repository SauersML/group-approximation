import GroupApproximation.CharClass.CartanGroupRing
import Mathlib.LinearAlgebra.TensorProduct.Basic

/-!
# The diagonal of the periodic resolution: its arithmetic core

The internal Cartan comparison uses the diagonal of the periodic resolution,

```text
Δ_W (e_n) = ∑_{i+j=n} e_i ⊗ T^i e_j ,
```

as bookkeeping inside the second composite `B`.  This file isolates the one
piece of mathematics in "`Δ_W` is a chain map" — a cancellation in the tensor
square of the group ring — and proves it.

## Why the object `W ⊗ W` is deliberately not constructed

`Δ_W` never has to exist as a morphism of chain complexes.  The source of the
comparison, `W ⊗ S(X)`, is **free** over the group ring on the pairs
`(i, σ)`, so both composites `A` and `B` are defined by their values on that
basis and extended `Λ`-linearly; `Δ_W` then enters only as the index sum
`∑_{i+j=n}` with the coefficient `T^i`, and what has to be checked is that `B`
is a chain map.  Unwinding that check on a basis element produces exactly the
identity below, once for each pair `(i, j)`.  Building `W ⊗ W` as a complex
would mean building a tensor product **over `ZMod 2`** of two complexes of
`Λ`-modules with the diagonal action — a different operation from Mathlib's
monoidal product on `ChainComplex (ModuleCat Λ)`, which tensors over `Λ` — and
none of it would be used.

## The identity

Over `ℤ` the standard resolution alternates `1 − T` and `1 + T`; mod `2` they
coincide, so `∂ e_i = (1 + T) e_{i-1}` in every degree and no sign ever appears.
Expanding `∂ Δ_W(e_n)` and `Δ_W(∂ e_n) = (1+T)·Δ_W(e_{n-1})` and comparing the
coefficients of `e_i ⊗ e_j` for `i + j = n - 1` gives

```text
(1+T) ⊗ T^{i+1}  +  1 ⊗ (T^i + T^{i+1})   =   1 ⊗ T^i  +  T ⊗ T^{i+1},
```

an identity in `Λ ⊗_{ZMod 2} Λ`.  It holds because the two copies of
`1 ⊗ T^{i+1}` produced on the left cancel in characteristic two — which is the
whole reason the mod-2 diagonal is sign-free.  Note the right-hand side is the
diagonal action `(1 + T)·(e_i ⊗ T^i e_j) = e_i ⊗ T^i e_j + T e_i ⊗ T^{i+1} e_j`,
not a `(1+T)` applied to one factor.
-/

namespace GroupApproximation.CharClass

open scoped TensorProduct

/-- The tensor square of the group ring has characteristic two. -/
lemma tensorSquare_add_self (x : GroupRingZ2 ⊗[ZMod 2] GroupRingZ2) : x + x = 0 := by
  rw [← two_smul (ZMod 2) x, show (2 : ZMod 2) = 0 from by decide, zero_smul]

/-- **The chain-map identity for `Δ_W`, as an identity of coefficients.**

The left-hand side is the coefficient of `e_i ⊗ e_j` in `∂ Δ_W(e_{i+j+1})`: the
first summand comes from differentiating the left tensor factor and the second
from differentiating the right one.  The right-hand side is its coefficient in
`(1+T)·Δ_W(e_{i+j})`, the diagonal action applied to the diagonal one degree
down.  The two agree because `1 ⊗ T^{i+1}` occurs twice on the left. -/
theorem deltaW_chain_identity (i : ℕ) :
    (1 + groupRingGen) ⊗ₜ[ZMod 2] (groupRingGen ^ (i + 1))
        + (1 : GroupRingZ2) ⊗ₜ[ZMod 2]
            (groupRingGen ^ i + groupRingGen ^ (i + 1))
      = (1 : GroupRingZ2) ⊗ₜ[ZMod 2] (groupRingGen ^ i)
        + groupRingGen ⊗ₜ[ZMod 2] (groupRingGen ^ (i + 1)) := by
  rw [TensorProduct.add_tmul, TensorProduct.tmul_add]
  calc (1 : GroupRingZ2) ⊗ₜ[ZMod 2] (groupRingGen ^ (i + 1))
        + groupRingGen ⊗ₜ[ZMod 2] (groupRingGen ^ (i + 1))
        + ((1 : GroupRingZ2) ⊗ₜ[ZMod 2] (groupRingGen ^ i)
          + (1 : GroupRingZ2) ⊗ₜ[ZMod 2] (groupRingGen ^ (i + 1)))
      = ((1 : GroupRingZ2) ⊗ₜ[ZMod 2] (groupRingGen ^ (i + 1))
          + (1 : GroupRingZ2) ⊗ₜ[ZMod 2] (groupRingGen ^ (i + 1)))
        + ((1 : GroupRingZ2) ⊗ₜ[ZMod 2] (groupRingGen ^ i)
          + groupRingGen ⊗ₜ[ZMod 2] (groupRingGen ^ (i + 1))) := by abel
    _ = 0 + ((1 : GroupRingZ2) ⊗ₜ[ZMod 2] (groupRingGen ^ i)
          + groupRingGen ⊗ₜ[ZMod 2] (groupRingGen ^ (i + 1))) := by
        rw [tensorSquare_add_self]
    _ = (1 : GroupRingZ2) ⊗ₜ[ZMod 2] (groupRingGen ^ i)
        + groupRingGen ⊗ₜ[ZMod 2] (groupRingGen ^ (i + 1)) := zero_add _

/-- The degree-zero normalization of the diagonal: `Δ_W(e_0) = e_0 ⊗ e_0`, whose
coefficient is `1 ⊗ 1`, since the only pair with `i + j = 0` is `(0, 0)` and
`T^0 = 1`. -/
theorem deltaW_zero_coeff :
    (1 : GroupRingZ2) ⊗ₜ[ZMod 2] (groupRingGen ^ 0)
      = (1 : GroupRingZ2) ⊗ₜ[ZMod 2] (1 : GroupRingZ2) := by
  rw [pow_zero]

end GroupApproximation.CharClass
