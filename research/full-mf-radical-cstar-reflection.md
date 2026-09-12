---
rg: 2
id: full-mf-radical-cstar-reflection
kind: claim
title: Full group radical collapses the maximal and reduced group C-star MF reflections
distinct_from:
  exact-stably-finite-non-mf-reduced-group-algebra: that claim proves one reduced group C-star algebra is non-MF; this theorem determines every homomorphism from both group C-star completions into every MF C-star algebra.
  universal-mf-quotient: that theorem is group-valued; this theorem computes the corresponding C-star-algebraic intersections of kernels.
artifacts:
  - research/full-mf-radical-cstar-reflection-proof.md
---

Let `G` be a countable group satisfying

```text
Rad_MF(G)=G.
```

For a unital C-star algebra `C`, write

```text
J_MF(C) = intersection ker(phi),
```

where `phi` ranges over all star homomorphisms from `C` to MF C-star
algebras; the homomorphisms are not required to be unital.

Then:

```text
J_MF(C*_max(G)) = ker(epsilon),                   (C1)
```

where `epsilon : C*_max(G) -> C` is augmentation.  More precisely, every
star homomorphism `phi : C*_max(G) -> A` with `A` MF has the form

```text
phi(x) = epsilon(x) p,   p=phi(1).
```

If `G` is nonamenable, then

```text
J_MF(C*_r(G)) = C*_r(G).                          (C2)
```

Equivalently, every star homomorphism from `C*_r(G)` to an MF C-star algebra
is zero.  Consequently:

1. the only nonzero MF image of `C*_max(G)` is scalar;
2. `C*_r(G)` has no nonzero MF quotient;
3. every nonzero quotient of `C*_r(G)` is non-MF;
4. every quasidiagonal quotient of `C*_r(G)` is zero.

This is stronger than non-MF-ness of the two group C-star algebras: it
computes their complete MF-visible parts.

