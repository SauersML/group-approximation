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

**Correction (2026-09-13, lane ex-fp-kazhdan-titz-witzel). OPEN, not established.**
- The proof route `titz-witzel-exact-kazhdan-mf-radical-over-z-proof` requires
  `simple-kazhdan-groups-have-full-mf-radical`. That claim is refuted by
  `simple-kazhdan-lef-group-from-minimal-subshift`. Its step "MF implies weakly quasidiagonal"
  fails for groups (`operator-mf-group-not-weakly-quasidiagonal-exists`).
- So the MF clause below is unproved, and so are "`G` is non-MF" and `(TWE2)`.

What survives, for `G = K x Z` with `K` a Titz Mite--Witzel residual:
- `G` is finitely presented and torsion-free, and `K` is finitely presented, infinite, simple
  and Kazhdan (`titz-witzel-simple-kazhdan-cat0-lattices-exist`).
- `Rad_MF(G) <= K x {0}`, because `G -> Z` has an MF target.

Moreover the open clause is equivalent to non-MF-ness of `K`:
- If `K` is not MF, then every homomorphism from `K` to an MF group has kernel `K` (simplicity).
  So `Rad_MF(G) = K`.
- If `K` is MF, then `(k,m) |-> diag(u(k), v(m))`, for embeddings `u` of `K` and `v` of `Z` into
  norm-corona unitary groups, embeds `G` in the unitary group of the norm corona of the block
  sizes. So `G` is MF and `Rad_MF(G) = 1`.

So `(TWE1)` holds exactly when `K` is not MF. Whether any finitely presented infinite simple
Kazhdan group is MF is open. By `kazhdan-mf-hyperlinear-fragment`, a simple Kazhdan MF group is
hyperlinear, so the failure of this claim would make `K` hyperlinear.

The original statement follows.

There exist a group `G` and a nontrivial normal subgroup
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

**2026-09-13.** The paragraph above predates the correction: the MF clause is open as well.

DERIVATION
titz-witzel-exact-kazhdan-mf-radical-over-z-proof
