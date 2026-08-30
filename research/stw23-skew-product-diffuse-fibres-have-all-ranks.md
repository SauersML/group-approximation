---
rg: 2
id: stw23-skew-product-diffuse-fibres-have-all-ranks
kind: claim
title: Minimal skew products with one Lebesgue-distributed fibre element have all ranks
distinct_from:
  stw99-problem-xxiii-rank-problem: that asks for every unital simple separable stably finite non-elementary algebra; this proves the rank conclusion for a concrete skew-product class with arbitrary invariant-measure simplex.
  stw99-problem-xi-zd-crossed-stably-finite-qd: that concerns quasidiagonality and AF-embeddability of stably finite crossed products; this theorem constructs positive elements with prescribed quasitracial ranks and does not assert quasidiagonality.
artifacts:
  - research/artifacts/stw23-skew-product-rank-realization-audit-2026-08-30.md
---

Let `X` be an infinite compact metrizable space, let `h:X->X` be a minimal
homeomorphism, and let `B` be a unital simple separable exact C*-algebra with
unique tracial state `tau_B`.  Suppose that there is a positive contraction
`b in B` with Lebesgue spectral distribution:

```text
tau_B(g(b)) = integral_[0,1] g(t) dt       for every g in C([0,1]).   (L)
```

For an arbitrary automorphism `beta` of `B`, put

```text
D = (C(X) tensor B) rtimes_(h tensor beta) Z.
```

Then `D` is unital, simple, separable, exact, stably finite, and
non-elementary, and **all ranks occur in `D`**: for every lower
semicontinuous affine

```text
f:QT(D) -> (0,infinity]
```

there is `a in (D tensor K)_+` such that

```text
d_sigma(a)=f(sigma)                    for every sigma in QT(D).      (R)
```

The construction is internal to the coefficient algebra: `a` may be chosen
in `(C(X) tensor B tensor K)_+`.  In particular, the theorem permits an
arbitrary metrizable invariant-measure simplex and an arbitrary skewing
automorphism on the noncommutative fibre; neither stable rank one, strict
comparison, nor Jiang--Su stability is used.
