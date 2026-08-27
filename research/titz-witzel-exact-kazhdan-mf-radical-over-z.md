---
rg: 2
id: titz-witzel-exact-kazhdan-mf-radical-over-z
kind: claim
title: A finitely presented torsion-free group has an exact proper Kazhdan MF radical and quotient Z
distinct_from:
  torsion-free-sofic-exact-mf-radical-over-z: That target additionally requires the total group to be sofic; every other clause is proved here, and its remaining soficity is the explicit three-permutation gate.
  titz-witzel-mapping-tori-are-virtually-products: That classifies every automorphism mapping torus of each of the five candidate kernels; this extracts the strongest unconditional existence theorem in direct-product form.
artifacts:
  - research/artifacts/titz-witzel-sofic-structure-audit-2026-08-26.md
---

**ESTABLISHED.**  There exist a group `G` and a nontrivial normal subgroup
`K normal G` such that

```text
G is finitely presented and torsion-free,
K is finitely presented, infinite, simple and has property (T),
Rad_MF(G)=K,                  G/K ~= Z.                 (TWE1)
```

The subgroup `K` is normally generated in `G` by every one of its nonidentity
elements.  The group `G` is non-MF, and for every countable MF group `M`,
precomposition with `G->Z` is a bijection

```text
Hom(Z,M) ~= Hom(G,M).                                  (TWE2)
```

Thus the requested torsion-free exact-radical theorem is unconditional in
every clause except soficity (and hence the requested route to
hyperlinearity).  For this witness, `G` is sofic exactly when `K` is sofic.
That single unresolved assertion is equivalent to the explicit
three-permutation, twelve-relator gate in
`titz-witzel-soficity-is-one-finite-csp`.

DERIVATION
titz-witzel-exact-kazhdan-mf-radical-over-z-proof
