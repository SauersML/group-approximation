---
rg: 2
id: stw27-stable-range-endpoint-division
kind: claim
title: Stable-range bundles split into n- and n+1-blocks and admit dimension-drop embeddings
distinct_from:
  stw27-low-rank-soft-divider-rounding: that theorem forces an alleged soft divider to be compact below rank n(n+1); this theorem constructs a compact divider for every bundle once its rank is sufficiently large relative to the base dimension.
  stw27-coordinate-euler-slack-obstructs-compact-dividers: that theorem gives a Chern obstruction in the coordinate-heavy range; this theorem shows that all characteristic-class obstructions disappear in a quantitative rank-dominant range by explicitly absorbing the reduced K-class into two endpoint bundles.
artifacts:
  - research/artifacts/stw27-dimension-drop-high-rank-audit-2026-08-30.md
---

Let `X` be a finite CW complex of covering dimension `d`, put

```text
D=ceil(d/2),
```

and let `E` be a complex vector bundle over `X` of constant rank `M`.  For
every integer `n>=2`, if

```text
M >= (2n+1)D + n(n-1),                                (H)
```

then there are vector bundles `F,G` such that

```text
E isomorphic to F^(direct_sum n) direct_sum G^(direct_sum (n+1)).   (2)
```

Consequently

```text
y=[F]+[G]
```

is a compact divider satisfying

```text
n y <= [E] <= (n+1)y.                                 (3)
```

In particular, the homogeneous corner `End(E)` admits a unital
star-homomorphism

```text
Z_(n,n+1) --> End(E)                                  (4)
```

obtained from the two endpoint representations of the prime dimension-drop
algebra.  Equivalently, this extends to a unital `C(X)`-linear map
`C(X) tensor Z_(n,n+1) --> End(E)`.

More precisely, the following are equivalent without any rank hypothesis:

1. there is a unital map `Z_(n,n+1)-->End(E)` which factors through the two
   endpoint quotient `M_n direct_sum M_(n+1)`;
2. `E` has a decomposition `nF direct_sum (n+1)G` for some vector bundles
   `F,G`.

Thus `(H)` is a uniform stable-range criterion forcing an endpoint-factoring
dimension-drop field; it does not assert that every dimension-drop field
must factor through the endpoints.

For a coordinate-Hopf Villadsen block over `(S^2)^N`, one has `D=N`.
Thus every rank-`M` bundle, independently of its Chern classes, has a compact
`n`-almost divider whenever

```text
M >= (2n+1)N+n(n-1).                                  (5)
```

In particular, the canonical Hopf image is divisible at every stage where
its matrix multiplicity crosses `(5)`.  This is a high-rank positive regime
for the precise finite-stage hinge in STW Problem XXVII(2).
