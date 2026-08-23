---
rg: 2
id: explicit-proper-d-completion-with-llp-exists
kind: claim
title: An explicit nonamenable group has a proper Brown-Guentner D-completion with LLP
artifacts:
  - research/artifacts/paulsen-harris-lalonde-tang-macmahon-source-audit-2026-08-23.md
distinct_from:
  non-rf-kazhdan-group-with-llp-full-c-star-algebra: that asks for LLP of a FULL group C-star algebra and pays for the conclusion with property (T) plus non-residual-finiteness; this asks for LLP of a proper intermediate representation completion and pays through the Paulsen--Rahaman--Samei obstruction.
  sp2g-z-full-c-star-algebra-has-llp: that is a specific full-completion LLP question for a symplectic lattice; this permits a different group and a proper representation quotient.
---

**OPEN CLAIM.**  Produce an explicit nonamenable discrete group `G` and
an explicit algebraic ideal

```text
c_00(G) subset D subset ell^infinity(G)
```

such that

```text
C^*(G) != C^*_D(G) canonically,
C^*_D(G) has Kirchberg's LLP.                          (EDL1)
```

By Paulsen--Rahaman--Samei Theorem 4.9 and
`llp-of-regular-dominating-nonamenable-completion-forces-nonhyperlinear`,
such a `G` is non-hyperlinear.  Thus the open LLP search should no longer
be restricted to full group C-star algebras of non-residually-finite
Kazhdan groups.

This is not known to be easier.  The reduced completion is already an
allowed endpoint of Theorem 4.9, and many familiar reduced group
C-star algebras fail LLP.  Also, LLP is not inherited by quotients, so
LLP of `C^*(G)` neither automatically supplies nor is required for
`(EDL1)`.  The new value is the extra choice of representation norm: one
may search among `ell^p`, ideal, and other intermediate completions while
retaining a theorem that closes the group goal.
