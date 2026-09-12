---
rg: 2
id: bernoulli-factors-to-infinite-stabilizer-coset-shifts-trivial
kind: claim
title: Every Borel equivariant map from a Bernoulli shift to a coset shift with infinite stabilizers is almost everywhere constant
distinct_from:
  full-shift-maps-to-infinite-stabilizer-coset-shifts-are-constant: that proves continuous equivariant maps from the full shift into such coset shifts are constant, using a finite window; this proves the same for Borel maps almost everywhere, using ergodicity of the infinite stabilizer on the Bernoulli shift.
  compressed-coset-shifts-carry-strict-equivariant-embeddings: that builds strict self-embeddings of a compressed coset shift; this shows the free Bernoulli shift has no nonconstant measurable factor into such a coset shift, so those embeddings cannot be pulled back onto it.
artifacts:
  - research/artifacts/measurable-alphabet-compression-2026-09-12.md
  - research/artifacts/gk-vf-nonlinear-verification-2026-09-12.md
---

Let `G` be a countable group, `K <= G` infinite, `A, B` finite, and `mu` the uniform product measure
on `A^G`. Every Borel map `F: A^G -> B^(G/K)` with `F(h.x) = h.F(x)` is `mu`-almost everywhere
constant.

*Proof sketch.* `f(x) = F(x)(K)` is `K`-invariant. The shift restricted to the infinite subgroup `K`
is mixing, so `f` is almost everywhere constant. Equivariance, invariance of `mu` and countably many
cosets give the same constant at every coset. Section 3 of the artifact.

**Consequence.** No measurable compression of the free shift over `U = L_(F_2)(1,2)^x` factors through
a coset shift `U/H` with `H` infinite, such as the compressed coset shift of
`compressed-coset-shifts-carry-strict-equivariant-embeddings`. Coset shifts with finite stabilizers
remain admissible codomains.

**ESTABLISHED 2026-09-12** by [[bernoulli-coset-shift-factors-trivial-proof]].
