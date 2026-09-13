---
rg: 2
id: primitive-projective-representations-have-a-trace-gap
kind: claim
title: In a primitive irreducible projective representation of a finite group X, non-scalar elements have |tr|/dim <= gamma(X), with gamma = 2^(-1/2) for solvable X
artifacts:
  - research/artifacts/ugc-rounding-normal-fibres-part2-2026-09-13.md
---

**ESTABLISHED.** Let `sigma` be an irreducible primitive projective
representation of a finite group `X`, with unitary normalization, and let
`sigma(h)` be non-scalar. Then

```text
|tr sigma(h)| <= gamma(X) dim sigma,     gamma(X) = max(2^(-1/2), gamma(T) : T a nonabelian simple section of X).
```

Here `gamma(T) < 1` is the largest `|tr A|/dim tau` over irreducible projective
representations `tau` of `T` of dimension at least `2` and non-scalar unitaries
`A` normalizing `tau(T)` up to scalars. It is a maximum over finitely many
values, because `T` is perfect, so `A` is determined up to a scalar by the
automorphism it induces. For solvable `X` there are no such sections, and the
bound is `2^(-1/2)`, independent of `X`.

* **Sharp.** A faithful 2-dimensional irreducible of `GL(2,3)` is primitive,
  and elements of order `8` have `|tr|/2 = 2^(-1/2)`.
* **`T` must enter.** The standard representation of `S_n`, `n >= 5`, is
  primitive, and a transposition has normalized trace `(n-3)/(n-1)`. So
  `gamma(A_n) -> 1`.
* **Mechanism.** Induct along a minimal normal subgroup `N/Z` above the scalar
  subgroup `Z`. Primitivity makes `N` homogeneous, and
  `sigma = taut (x) pit` with `pit` primitive for `X/N`. If `taut(h)` is
  scalar, induct. Otherwise, in the symplectic case (`N/Z` elementary
  abelian), the coefficients of `taut(h)` in the Heisenberg basis have constant
  modulus on cosets of `Im(g - 1)`, so `|tr|/dim <= p^(-1/2)`. In the
  tensor case (`N/Z = T^s`), either factors are permuted (ratio `<= 1/2`) or
  one factor carries a non-scalar normalizer (ratio `<= gamma(T)`).

This is a density analogue of Blichfeldt's theorem that a primitive element with
eigenvalues in an arc shorter than `pi/3` is scalar [recalled]. It is used by
`normal-fibre-galois-games-round-linearly-over-all-groups`, where Markov-type
rounding needs an average bound, not an all-eigenvalue bound. A bounded check
(recall only) did not locate this form; no novelty is claimed.
