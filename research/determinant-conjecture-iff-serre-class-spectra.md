---
rg: 2
id: determinant-conjecture-iff-serre-class-spectra
kind: claim
title: A group satisfies the determinant conjecture iff its integral self-adjoint spectra obey all Serre inequalities
distinct_from:
  determinant-conjecture: that is the conjecture for all groups; this is an exact one-variable reformulation valid group by group
  fk-transfer-needs-uniform-log-integrability: that concerns two-sided transfer of log determinants along moment limits; this is an exact equivalence at a single group, with no limits in it
artifacts:
  - research/artifacts/determinant-conjecture-serre-class-2026-09-11.md
---

**ESTABLISHED (written proof, artifact Section 1).** For every group `G` the
following are equivalent.

1. `det_N(G)(B) >= 1` for every `B in M_{m x n}(Z[G])`.
2. For every `n`, every self-adjoint `A in M_n(Z[G])`, and every nonzero
   `Q in Z[x]`,

   ```text
   integral_{Q != 0} log |Q(lambda)| d mu_A(lambda) >= 0.
   ```

The conjecture is therefore a statement about single operators, one variable
at a time. It asks nothing about approximating `G`; it asks whether every
integral group-ring spectrum lies in the Serre class of measures.
