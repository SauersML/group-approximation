---
rg: 2
id: invertible-difference-permutation-module-proof
kind: route
title: Project to alpha-orbits, kill the infinite orbits by (t-1)-adic valuation, and read off a finite-dimensional span
target: invertible-difference-modules-are-not-permutation-submodules
requires: []
artifacts:
  - research/artifacts/solve-bh-apapa-2026-09-13.md
---

**Orbit decomposition.** `Omega` is the disjoint union of its `<alpha>`-orbits,
so `K[Omega]` is the direct sum of the subspaces `K[O]`. Each projection
`pi_O : K[Omega] -> K[O]` (restriction of a function to `O`) commutes with
`alpha`, because `alpha` maps `O` to itself.

**Infinite orbits contribute nothing.** Let `O` be an infinite orbit and fix
`x_0 in O`. The map `alpha^n x_0 -> t^n` identifies `K[O]` with the Laurent
polynomial ring `K[t, t^-1]`, and `alpha` acts as multiplication by `t` (it sends
the indicator of `alpha^n x_0` to the indicator of `alpha^(n+1) x_0`). So
`alpha - 1` acts as multiplication by `t - 1`.

Let `v in V`. Since `alpha - 1` maps `V` onto `V`, choose `v_1, v_2, ... in V`
with `v = (alpha - 1)^n v_n` for every `n >= 1`. Applying `pi_O`,

```text
pi_O(v) = (t - 1)^n pi_O(v_n)     in K[t, t^-1],   for every n >= 1.           (DV)
```

If `pi_O(v) != 0`, write `pi_O(v) = t^e g` with `g in K[t]`, `g(0) != 0`. Then
`(DV)` makes `(t - 1)^n` divide `g` in `K[t, t^-1]`, hence in `K[t]` (the only
units of `K[t, t^-1]` are `c t^m`, and `t` is prime to `t - 1`). So `n <= deg g`
for every `n`, which is impossible. Hence `pi_O(v) = 0` for every infinite orbit.

**Finite span.** `v` has finite support, and by the previous step that support
meets only finite orbits `O_1, ..., O_r`. The subspace
`K[O_1 ∪ ... ∪ O_r]` has dimension `|O_1| + ... + |O_r|`, is invariant under
`alpha` and `alpha^-1`, and contains `v`. So it contains every `alpha^m v`, and
the span of the `alpha`-orbit of `v` is finite-dimensional. If `K` is finite,
that span is a finite set, so `alpha^m v = v` for some `m >= 1`. `∎`

Injectivity of `alpha - 1` on `V` is not used; surjectivity is what gives `(DV)`.
