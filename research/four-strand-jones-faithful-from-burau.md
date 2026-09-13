---
rg: 2
id: four-strand-jones-faithful-from-burau
kind: route
title: "Jones representation of B_4 is faithful once Burau is: the kernel of a representation lies in the kernel of each summand"
target: four-strand-jones-representation-is-faithful
requires:
  - four-strand-burau-representation-is-faithful
---

Let `J` be Jones's representation of `B_4`, defined over a Laurent polynomial ring in the Hecke
parameter.

**Summand input** (Jones 1987, as quoted in arXiv:2607.05283v1; not re-read here). Over the fraction
field at generic parameter, `J` is a direct sum of irreducible representations, one of which is
the reduced Burau representation `ρ_4`, possibly after two changes that do not affect kernels:

- substituting `t ↦ q^{±1}`, a ring automorphism;
- twisting by a character `σ_i ↦ u` (`u` a unit).

**Derivation.**

1. If `J(x) = I`, then `x` acts as the identity on every summand. The kernel over the ring equals
   the kernel over its fraction field.
2. Untwisted summand: `ρ_4(x) = I`, so `x = 1` by `four-strand-burau-representation-is-faithful`.
3. Twisted summand: `ρ_4(x) = u^{-e(x)} I`, where `e : B_4 → Z` is the exponent sum. Taking
   determinants, `((-t)·u^3)^{e(x)} = 1`. `u` is a unit of the coefficient ring, a signed monomial
   in the parameter, so `(-t)·u^3 = ±t^k` for some integer `k`. If `k ≠ 0`, this forces
   `e(x) = 0`. If `k = 0`, use the one-dimensional summand of the row partition, where `σ_i` acts
   by a non-root-of-unity scalar (Jones 1987): there `J(x) = I` also gives `e(x) = 0`. Either way
   `ρ_4(x) = I` and `x = 1`. ∎

The summand structure is the only imported input. The derivation is elementary.
