---
rg: 2
id: locally-residually-finite-targets-kill-compression-defects
kind: claim
title: Every homomorphism to a locally residually finite group kills the compression defect of a finitely generated subgroup
distinct_from:
  compression-defect-dies-in-finite-dimensions: that kills the defect in every finite-dimensional linear representation by a commutant-dimension argument; this kills it in every locally residually finite target by a finite-group cardinality argument, with no linearity, and is what the finite-rank kernel theorem consumes for the quotient step.
  kazhdan-defects-vanish-in-central-quotients-of-rf-groups: that computes the defect inside a central quotient of a residually finite group and needs property (T) of the compressed subgroup; this is a statement about homomorphisms out of an arbitrary group into a locally residually finite target and uses no property (T).
  locally-rf-by-amenable-cannot-supply-exact-kazhdan-kernel: that is about Kazhdan subgroups of a locally-RF-by-amenable group being residually finite; this is about compression defects being killed by maps into locally residually finite groups.
artifacts:
  - research/artifacts/finite-rank-compression-defect-dichotomy-2026-09-09.md
---

**ESTABLISHED.**  For `L <= G` write

```text
D_G(L) = << [u c u^-1, l] : u L u^-1 <= L,  c in C_G(L),  l in L >>_G
```

for the compression--centralizer defect.  Call a group *locally
residually finite* when each of its finitely generated subgroups is
residually finite; the whole group need not be residually finite.

Let `L <= G` be finitely generated, let `Q` be locally residually finite,
and let `phi : G -> Q` be a homomorphism.  Then

```text
phi(D_G(L)) = 1.                                                   (LRF)
```

No property (T), finiteness, centrality, or normality enters.  Examples of
`Q`: every finite group, every residually finite group, every directed
union of residually finite groups, `GL_d(Q)` (a finitely generated
subgroup lies in `GL_d(Z[1/m])` and reduction modulo primes not dividing
`m` separates it), and `GL_n(Z[z,z^-1])`.

**Why it matters.**  It is the quotient step of
`finite-rank-kernel-forces-abelian-defect-subgroups`: a normal subgroup
`N` whose quotient `G/N` is locally residually finite absorbs the entire
defect, `D_G(L) <= N`.  Over a field, the finite-dimensional case of
`(LRF)` is also `compression-defect-dies-in-finite-dimensions` combined
with Malcev's theorem; the cardinality proof here avoids Malcev, and the
dimension proof there avoids finite quotients.

**What it does not say.**  Nothing about `G` itself being residually
finite, and nothing about MF targets: the manuscript's group `W` is
(locally residually finite)-by-`Z` with a nontrivial defect, so a locally
residually finite *kernel* does not kill the defect, only a locally
residually finite *target* does.

Derivation: `locally-residually-finite-targets-kill-compression-defects-proof`.
