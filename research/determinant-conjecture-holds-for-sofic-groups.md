---
rg: 2
id: determinant-conjecture-holds-for-sofic-groups
kind: claim
title: Sofic groups satisfy the Fuglede--Kadison determinant conjecture
distinct_from:
  determinant-conjecture: that is the universal conjecture; this is the sofic case, imported from the literature
---

**ESTABLISHED (literature import).** For every sofic group `G` and every
`A in M_{m x n}(Z[G])`, `det_N(G)(A) >= 1`. Source: G. Elek and E. Szabó,
*Hyperlinearity, essentially free actions and L^2-invariants. The sofic
property*, Math. Ann. 332 (2005).

The proof has exactly the shape isolated in
`integral-spectral-limits-satisfy-serre-inequalities`: a sofic model of `A` is
an integer matrix, its spectral measures converge weakly to `mu_(A^*A)`, and
integrality of every approximant carries the inequality to the limit.
