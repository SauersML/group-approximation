---
rg: 2
id: stw99-lxxvi-one-dimensional-formation-preserves-cu-regularity
kind: claim
title: One-dimensional formation preserves Cu-regularity at the idealwise K1-free boundary
distinct_from:
  stw99-lxxvi-circle-formation-preserves-cu-regularity: the circle theorem permits arbitrary K1 by retaining the compact clutching summand; this theorem permits every second-countable locally compact base of dimension at most one because idealwise K1-vanishing makes the whole Cu computation pointwise.
artifacts:
  - research/artifacts/stw99-lxxvi-fourth-depth-audit-2026-08-30.md
---

Let `X` be a second-countable locally compact Hausdorff space with covering
dimension at most one, let `B` be a separable C*-algebra, and put

```text
E=B tensor_min Z.
```

Suppose that:

1. `B` and `E` have stable rank one;
2. `K_1(I)=0` for every closed two-sided ideal `I` of `B` and of `E`; and
3. the actual first-factor map `Cu(B)->Cu(E)` is an isomorphism.

Then `C_0(X,B)` is Cuntz semigroup regular.  More precisely, evaluation gives
natural isomorphisms

```text
Cu(C_0(X,B))              ~= Lsc(X,Cu(B)),
Cu(C_0(X,E))              ~= Lsc(X,Cu(E)),                 (1)
```

under which the first-factor map for `C_0(X,B)` is pointwise application of
`Cu(B)->Cu(E)`, and hence is an isomorphism.

Consequently, if `D` is simple, separable, stably finite, and pure with
`K_1(D)=0`, then `C_0(X,D)` is both pure and Cuntz semigroup regular.  This
includes arbitrary noncompact one-dimensional spaces and bases with infinite
branching or infinitely many cycles, not only finite graphs.
