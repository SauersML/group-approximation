---
rg: 2
id: matrix-recovery-of-schur-flip-wreath-sites
kind: claim
title: Matrix microstates recover enough new Schur flip wreath sites to outrun multiplicity
artifacts:
  - research/artifacts/schur-clifford-predicate-rank-compiler-2026-08-19.md
  - notes/TRUE_RELATIVE_WALL_IS_COMMUTANT_GROWTH.md
distinct_from:
  schur-flip-wreath-compressor-has-infinite-cocycle-rank: that constructs arbitrary cocycle rank in the exact Bernoulli model; this must recover more than `log_2 m` independent site factors from a finite-dimensional approximate representation with uniform HS loss.
  supercritical-network-needs-noncanonical-cuts: that rules out supercriticality for canonical fixed trace cuts; this explicitly requires a microstate-dependent stopping rule at the current external multiplicity.
---

For a finite presentation containing the Schur flip wreath/compressor window,
prove the following normalized-HS rounding statement.  On a forbidden packet
carrier of external multiplicity `m`, every sufficiently accurate matrix
microstate either pays a fixed relator-energy floor or admits

```text
n>log_2 m
```

new compressor-site factors whose two local flip implementers:

1. exactify to the prescribed finite packet automorphisms;
2. have pairwise tensor-independent coefficient algebras on the carrier;
3. have cross-commutators small enough that the aggregate binary cocycle form
   has rank `2n` after dimension-independent correction; and
4. return to the original fixed packet scale with total squared error at most
   `C E_rel`, where `C` is independent of `m,n`, and the chosen sites.

The site set must be selected from finite-multiplicity data of the current
microstate; selecting any fixed canonical finite window is insufficient.

## Attempts

- Exact site growth alone is not soundness: every fixed finite site tensor
  window is finite dimensional and admits arbitrarily large amplifications,
  regardless of whether the full crossed-product trace is Connes embeddable.
- Ordinary word-by-word recovery accumulates error with the number and word
  lengths of the selected sites.
- The active possibility is property-(T) orbit averaging plus a
  microstate-dependent spectral cutoff of the relative-commutant inclusion.
  Infinite exact index supplies arbitrarily many directions, while scaled
  Kazhdan transport is already valid at the cutoff's own rank scale.  What is
  missing is a finite-word coordinate theorem turning those directions into
  distinct local flip factors.
- `infinite-index-does-not-force-supercritical-site-rank` shows that even such
  coordinate recovery at every fixed rank is insufficient.  Exact `n`-site
  windows already have multiplicity `2^nL`.  The theorem must be genuinely
  diagonal: after the spectator multiplicity `L` is present, it must activate
  more cells in the same model, with a constant-gap semantic return.
