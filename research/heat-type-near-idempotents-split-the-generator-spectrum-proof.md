---
rg: 2
id: heat-type-near-idempotents-split-the-generator-spectrum-proof
kind: route
title: Bound the scalar function lambda(1-lambda) on the spectrum and transport it through the exponential
target: heat-type-near-idempotents-split-the-generator-spectrum
requires: []
artifacts:
  - research/artifacts/fd-compressor-commutant-and-cycle-rounding-2026-09-12.md
---

`A >= 0` self-adjoint on `(M_D, ||·||_2)`, `Phi = exp(-tA)` unital and trace
preserving. `Phi` is self-adjoint for `<x,y> = tr(x*y)`, so it is diagonalizable
with real spectrum, and `spec(Phi) = {e^(-t mu) : mu in spec(A)}` is contained in
`(0,1]`.

**1. The scalar inequality.** `Phi^2 - Phi` is the functional calculus of
`lambda -> lambda^2 - lambda`, so

```text
||Phi^2 - Phi||_(2->2) = max{ |lambda^2 - lambda| : lambda in spec(Phi) }
                       = max{ lambda(1-lambda) : lambda in spec(Phi) },
```

the second equality because `lambda` lies in `(0,1]`, where `lambda^2 <= lambda`.
So the hypothesis says `lambda(1-lambda) <= delta` for every eigenvalue.

**2. Solving it.** For `delta < 1/4` the set `{lambda in [0,1] : lambda(1-lambda)
<= delta}` is `[0, l_-] ∪ [l_+, 1]` with `l_± = (1 ± sqrt(1-4delta))/2`. Since
`sqrt(1-4delta) >= 1-4delta` on `[0,1/4]`, we get `l_- <= 2delta` and
`l_+ >= 1-2delta`. Hence

```text
spec(Phi) is contained in (0, 2delta] ∪ [1-2delta, 1].
```

**3. Transport to the generator.** `lambda = e^(-t mu)` is decreasing in `mu`, so
`lambda >= 1-2delta` iff `mu <= -log(1-2delta)/t = a`, and `lambda <= 2delta` iff
`mu >= log(1/(2delta))/t = b`. Therefore `spec(A)` is contained in
`[0,a] ∪ [b, infinity)`. For small `delta`, `a = 2delta/t + O(delta^2/t)` and
`b = log(1/(2delta))/t`, so `b/a -> infinity`.

**4. Proximity to the band projection.** Let `P` be the spectral projection of `A`
onto `[0,a]`, equivalently of `Phi` onto `[1-2delta, 1]`. On that band
`|lambda - 1| <= 2delta`, and on the complementary band `|lambda - 0| <= 2delta`.
Both maps are functional calculus of the same self-adjoint operator, so

```text
||Phi - P||_(2->2) = max{ |lambda - 1[lambda >= 1-2delta]| } <= 2delta.
```

QED

**5. The fixed-point remark.** `ker A` is the set of `x` with `Phi_s(x) = x` for
all `s`, the fixed-point set of a unital trace-preserving CP semigroup, hence a
`*`-subalgebra, and the orthogonal projection onto it is the trace-preserving
conditional expectation. So when the low band is exactly `ker A` the map rounds,
with constant `2delta`, and any counterexample needs the band to be strictly
larger.
