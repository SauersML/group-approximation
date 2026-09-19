---
rg: 2
id: finite-order-unitary-has-uniform-opnorm-gap-proof
kind: route
title: The spectrum sits on N-th roots of unity and the norm is the largest chord
target: finite-order-unitary-has-uniform-opnorm-gap
requires: []
---

`u` is unitary, hence normal, so `u-1` is normal and

```text
||u - 1|| = max { |lambda - 1| : lambda in sigma(u) }.
```

From `u^N=1` the continuous functional calculus gives
`p(u)=0` for `p(z)=z^N-1`, so every `lambda in sigma(u)` satisfies
`lambda^N=1`; that is, `sigma(u)` is contained in the group `mu_N` of `N`-th
roots of unity.

If `sigma(u) = {1}` then `u = 1` by normality (a normal element with
one-point spectrum is that scalar). Since `u != 1`, there is
`zeta in sigma(u)` with `zeta != 1` and `zeta^N = 1`. Hence

```text
||u - 1|| >= |zeta - 1| >= min { |xi - 1| : xi^N = 1, xi != 1 }.
```

The minimum is attained at a primitive-angle neighbour
`xi = e^(2 pi i / N)`, and

```text
|e^(2 pi i / N) - 1| = 2 |sin(pi/N)| = 2 sin(pi/N)
```

for `N >= 2`, giving `(TG2)`.

The proof uses only normality and the functional calculus, so it holds
verbatim in any unital C*-algebra, and in particular unchanged in the norm
matrix corona, where `u^N=1` is an exact equation in the quotient.

**Dilution invariance.** For a unital embedding `A -> B` the norm is
preserved, so `||(u ⊕ 1_D) - 1|| = max(||u-1||, 0) = ||u-1||`. For the
tensor amplification, `(u ⊗ I_k) - 1 = (u-1) ⊗ I_k` and the operator norm is
multiplicative on tensor products of this form, so
`||(u ⊗ I_k) - 1|| = ||u-1||`. Neither identity involves a normalization,
which is the whole content of the exclusion test.
