---
rg: 2
id: finite-schur-clifford-packet-flexible-hs-exactification
kind: claim
title: Each fixed Schur-Clifford packet flexibly exactifies with dimension-independent normalized-HS control
artifacts:
  - research/artifacts/schur-clifford-predicate-rank-compiler-2026-08-19.md
distinct_from:
  predicate-rank-gate-doubles-restriction-multiplicity: that computes the exact restriction multiplicities after a packet representation is exact; this reaches an exact representation from one approximate local packet.
  non-ce-bcs-has-robust-approximate-energy-gap: that controls all contexts simultaneously using the original shared selector words; this supplies the local exact packet sectors used to read their rank-jump mass.
  a4-triangle-hs-regular-core: that specializes flexible finite-group stability to an A4 triangle and then uses character values to extract a regular core; this applies the same finite-group mechanism to an arbitrary fixed Schur-Clifford packet and records its central sectors.
---

Fix one finite Schur--Clifford packet group `K(M)` with a finite presentation
and fixed normal-form words for all of its elements.  For every `eta>0` there
is `delta>0`, depending only on the fixed packet and `eta`, such that every
`d`-dimensional tuple whose packet relators have normalized-HS defect below
`delta` flexibly exactifies to an exact representation

```text
rho:K(M)->U(m),                    d <= m <= (1+eta)d,
```

whose compressed named generators are `eta`-close to the input tuple.

Consequently the exactified central involutions `J,z_1,...,z_k` have genuine
joint character projections.  Their traces differ by `O_K(eta)` from the
corresponding polynomial spectral masses of the input, and on every exact
sector the irreducible dimensions and `A_f<=B_f` restriction multiplicities
are exactly those of `clifford-commutator-rank-is-packet-dimension` and
`predicate-rank-gate-doubles-restriction-multiplicity`.

This is a **local** theorem.  Applying it independently in two contexts need
not give the same corrected copy of a shared selector.  The downstream route
does not identify those corrections: `non-ce-bcs-has-robust-approximate-energy-gap`
is applied first to the original globally shared words, and fixed-length
telescoping transfers their forbidden-product mass to the local exact packet
sectors.

When an actual comparison is needed, the pairwise obstruction is now
quantified by `finite-group-shared-overlap-polar-alignment`: two corrections
which approximate the same shared finite subgroup have exactly equivalent
restrictions on a submodule of dimension `d-O(eta^2 d)`. That lemma does not
by itself make a whole cyclic atlas compatible.
