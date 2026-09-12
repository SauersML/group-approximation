---
rg: 2
id: o2-zp-cartan-fixing-iff-rokhlin-uct-ascent-proof
kind: route
title: Pass to the dual action with Takai duality and apply the one-action Cartan criterion on both sides
target: o2-zp-cartan-fixing-iff-rokhlin-uct-ascent
requires: [barlak-li-p-half-iff-zp-actions-fix-cartan, izumi-rokhlin-approximately-representable-duality, uct-class-permanence-properties]
artifacts:
  - research/artifacts/uct-o2-cyclic-actions-2026-09-12.md
---

Throughout, identify `Ẑ_p` with `Z_p`. Part (a) of
`barlak-li-p-half-iff-zp-actions-fix-cartan` (Barlak--Li II, Corollary 4.15)
says: for outer, strongly approximately inner `α : Z_p ↷ O_2`, the crossed
product `O_2 ⋊_α Z_p` satisfies the UCT iff some Cartan subalgebra is
`α`-invariant.

**`Asc_p ⟹ D_p`.**  Let `α : Z_p ↷ O_2` be outer and strongly approximately
inner, and put `B = O_2 ⋊_α Z_p`.

1. `B` is a unital Kirchberg algebra. It is unital, separable and nuclear
   because `O_2` is and `Z_p` is finite. Because `α` is outer, `B` is simple and
   purely infinite. The proof of Barlak--Li II Theorem 4.12 derives both from
   outerness, citing Kishimoto, Commun. Math. Phys. 81 (1981), Theorem 3.1,
   and Jeong, Proc. Amer. Math. Soc. 123 (1995), Theorem 3.
2. By item 3 of `izumi-rokhlin-approximately-representable-duality`, `α` is
   approximately representable. By item 2 there, `δ := α̂` has the Rokhlin
   property.
3. Takai duality gives `B ⋊_δ Z_p ≅ O_2 ⊗ M_p`. That algebra is a unital
   Kirchberg algebra with trivial K-theory, and it satisfies the UCT because
   `O_2` does (item 4 of `uct-class-permanence-properties`). So it is
   isomorphic to `O_2` by Kirchberg--Phillips classification, the mechanism
   recorded in `kirchberg-uct-reduces-to-trivial-k-kirchberg-algebras`.
4. `Asc_p` now gives the UCT for `B`, and part (a) gives an `α`-invariant
   Cartan subalgebra.

**`D_p ⟹ Asc_p`.**  Let `B` and `δ` be as in `Asc_p`. Fix an isomorphism
`C := B ⋊_δ Z_p ≅ O_2`, and write `β := δ̂ : Z_p ↷ C`.

1. **Approximately representable.** This holds by item 2 of the duality claim,
   because `δ` has the Rokhlin property.
2. **Strongly approximately inner.** Approximate representability gives a
   unitary `u` in the sequence algebra of the unital algebra `C^β`, with
   `β_1(c) = u c u*` for all `c ∈ C`. Lift `u` to a bounded sequence
   `x_n ∈ C^β` with `x_n* x_n → 1` and `x_n x_n* → 1`. The unitaries
   `u_n := x_n |x_n|^(-1) ∈ C^β` (for large `n`) satisfy `β_1 = lim_n Ad(u_n)`
   pointwise in norm.
3. **Outer.** Suppose `β` is not outer. Since `p` is prime, `β_1 = Ad(v)` for a
   unitary `v ∈ C`. Then `v^p` is central, hence a scalar, and after rescaling
   `v^p = 1`. Also `β_1(v) = v`, so `v` commutes with the implementing unitary
   `w` of the crossed product. Now `z := v* w` is a unitary with `z^p = 1` that
   commutes with `C` and with `w`, so it is central in `C ⋊_β Z_p`. It is not a
   scalar, because its Fourier coefficient at `0` vanishes. Its spectral
   projections are then nontrivial central projections. But
   `C ⋊_β Z_p ≅ B ⊗ M_p` by Takai duality, and that algebra is simple.
   Contradiction.
4. **Conclusion.** Transported to `O_2`, `β` is outer and strongly
   approximately inner, so `D_p` gives a `β`-invariant Cartan subalgebra. Part
   (a) gives the UCT for `C ⋊_β Z_p ≅ B ⊗ M_p`. `B ⊗ M_p` is stably isomorphic
   to `B`, hence KK-equivalent to it, so `B` satisfies the UCT (item 1 of
   `uct-class-permanence-properties`).
