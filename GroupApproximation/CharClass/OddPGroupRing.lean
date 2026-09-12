import Mathlib.Algebra.MonoidAlgebra.Basic
import Mathlib.Data.ZMod.Basic
import Mathlib.Algebra.CharP.Algebra
import Mathlib.Algebra.CharP.Lemmas
import Mathlib.Algebra.Ring.GeomSum

/-!
# The mod-`p` group ring of `ℤ/p`, for `p` an odd prime

The odd-primary Steenrod reduced powers are built from the `ℤ/p`-equivariant
diagonal `W ⊗ C(X) → C(X)^{⊗p}`, and the acyclic-models theorem of
`AcyclicModels.lean` supplies that diagonal when it is instantiated at
`Λ := (ZMod p)[ℤ/p]`.  This file is that `Λ`, together with the three elements
the resolution and every equivariance argument are written in terms of.

`CartanGroupRing.lean` is the `p = 2` instance of this file's contents; it is
**not** edited and **not** replaced, because the mod-2 LIX answer is a verified
artifact and must keep building.  The two files coexist and share no name.

## The three elements, and the one identity that pays for everything

* `grGen p` is the class `T` of the generator of `ℤ/p`, with `T ^ p = 1`;
* `grS p` is `T - 1`;
* `grNorm p` is the norm `1 + T + ⋯ + T^{p-1}`.

The whole point of introducing `grS` is that

```text
    grNorm p * grS p = T ^ p - 1 = 0
```

is a *telescoping* identity (`geom_sum_mul`), so the chain-complex condition of
the standard periodic resolution — whose two alternating differentials are
multiplication by `grS` and by `grNorm` — costs one rewrite and no case split.
At `p = 2` the two elements coincide (`T - 1 = T + 1`) and the classical
resolution collapses to a single repeated differential, which is exactly the
collapse `AcyclicModelsResolution.lean` records; at odd `p` they do not, and the
resolution genuinely alternates.

The Frobenius consequence `grS p ^ p = 0` needs `Λ` to have characteristic `p`
and lives in `OddPFrobenius.lean`, deliberately in a file of its own: the
resolution needs only `grNorm_mul_grS`, so nothing downstream of this file should
be blocked by the characteristic argument.
-/

namespace GroupApproximation.CharClass

/-- **The mod-`p` group ring of `ℤ/p`.**  A commutative ring, since `ℤ/p` is
abelian, so `AcyclicModels.lean`'s `[CommRing Λ]` is satisfied. -/
abbrev GroupRingZMod (p : ℕ) : Type := MonoidAlgebra (ZMod p) (Multiplicative (ZMod p))

/-- The class `T` of the generator of `ℤ/p` inside the group ring. -/
noncomputable def grGen (p : ℕ) : GroupRingZMod p :=
  MonoidAlgebra.single (Multiplicative.ofAdd (1 : ZMod p)) (1 : ZMod p)

/-- `T ^ p = 1`: the generator has order dividing `p`. -/
theorem grGen_pow_card (p : ℕ) : grGen p ^ p = 1 := by
  unfold grGen
  rw [MonoidAlgebra.single_pow, one_pow, ← ofAdd_nsmul]
  have hp : (p : ℕ) • (1 : ZMod p) = 0 := by
    rw [nsmul_eq_mul, mul_one, ZMod.natCast_self]
  rw [hp, ofAdd_zero, ← MonoidAlgebra.one_def]

/-- `s := T - 1`.  The first differential of the periodic resolution is
multiplication by this element. -/
noncomputable def grS (p : ℕ) : GroupRingZMod p := grGen p - 1

/-- The norm `N := 1 + T + ⋯ + T^{p-1}`.  The second differential of the periodic
resolution is multiplication by this element. -/
noncomputable def grNorm (p : ℕ) : GroupRingZMod p := ∑ j ∈ Finset.range p, grGen p ^ j

/-- **The chain-complex identity**, telescoping: `N · (T - 1) = T^p - 1 = 0`. -/
theorem grNorm_mul_grS (p : ℕ) : grNorm p * grS p = 0 := by
  unfold grNorm grS
  rw [geom_sum_mul, grGen_pow_card, sub_self]

/-- The same identity in the other order; the ring is commutative. -/
theorem grS_mul_grNorm (p : ℕ) : grS p * grNorm p = 0 := by
  rw [mul_comm]; exact grNorm_mul_grS p

end GroupApproximation.CharClass
