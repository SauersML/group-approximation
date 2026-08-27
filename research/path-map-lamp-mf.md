---
rg: 2
id: path-map-lamp-mf
kind: claim
title: Path-MAP lamps over a compressed site space form an MF group
distinct_from:
  infinite-cyclic-compression-lamp-mf: That claim is the scalar case, lamps `Z` represented by slow phases; this one replaces the phase by a path of genuine finite-dimensional representations, and covers nonabelian lamps such as free groups.
---

Credit: external review session (2026-08-15, unrefereed); audited at
architecture level by this session.

Call a countable group `K` **path-MAP** if every nontrivial element of
`K` is detected by some finite-dimensional unitary representation lying
in the same path component of `Hom(K, U(d))` as the trivial
representation.  Free groups are path-MAP (`Hom(F_r, U(d)) = U(d)^r` is
path-connected); nontrivial property-(T) groups are never path-MAP (the
trivial representation is isolated by a Kazhdan pair); path-MAP groups
are torsion-free.

Let `H` be countable residually finite, `L <= H` finitely generated,
`L_1 = t L t^{-1} < L`, and `X = H/L_1`.  If `K` is path-MAP, then

```text
K^(X) semidirect H     is MF.
```

**Consequences.**  The diffuse escape of
`infinite-cyclic-compression-lamp-mf` is not an abelian accident: free
lamps escape too.  The conceptual duality is Kazhdan rigidity of the base
versus representation-theoretic deformability-to-1 of the lamp, matching
the discrete/connected spectral dichotomy of
`spectral-component-motion-bound` on the obstruction side.
