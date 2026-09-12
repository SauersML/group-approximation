---
rg: 2
id: deligne-rank-models-carry-no-bounded-block-mass
kind: claim
title: In rank-approximate projective representations of the Deligne multiplier, bounded invariant blocks carry vanishing mass
distinct_from:
  maslov-bounded-block-sector-gap: that is a normalized Hilbert--Schmidt gap for unitary tuples, proved by compactness in each bounded matrix size with no explicit constant; this is a normalized-rank bound over every field of characteristic p != 3, with the explicit constant m|R_0|, proved by integrality of rank.
  deligne-monomial-twisted-modules-have-no-folner-truncations: that excludes coordinate truncations of one fixed monomial module; this excludes direct sums of bounded-dimensional pieces, monomial or not.
artifacts:
  - research/artifacts/deligne-rank-projective-rigidity-2026-09-12.md
---

Let `Gamma = Sp_4(Z)`, `E_3` Deligne's triple cover with normalized cocycle `a`, `p != 3` a prime, `j in {1, 2}`,
and `w` a primitive cube root of unity. There are a finite `B_0 <= Gamma` and a finite set `R_0` of pairs in it
with the following property.
- **Setting.** Let `K` be a field of characteristic `p` containing `w`, and let `rho : B -> GL_d(K)` with
  `B >= B_0` satisfy `rank(rho(g)rho(h) - w^(j a(g,h)) rho(gh)) <= eps d` for `(g, h) in R_0`.
- **Statement.** If `K^d` is a direct sum of subspaces invariant under `rho(B_0)`, the summands of dimension at
  most `m` carry at most `m |R_0| eps` of the dimension.

So in vanishing-defect families the mass on bounded-dimensional packets tends to zero, uniformly in the
dimension and the field. A rank-approximate projective representation of the Deligne multiplier must be
large-block on asymptotically all of its dimension.

**ESTABLISHED 2026-09-12** by `deligne-rank-bounded-block-mass-proof` (artifact Lemma 0.1 and Proposition 1.1).
Verification requested from w4-vf-linear-b.
