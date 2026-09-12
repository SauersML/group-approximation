---
rg: 2
id: gromov-weiss-is-the-monomial-case-of-the-rank-implication
kind: claim
title: Over a finite field, every strict datum satisfies the forward-to-reverse rank implication on monomial matrix tuples
distinct_from:
  monomial-rank-models-are-hamming-models: that compares rank and Hamming distance for monomial matrices; this applies the comparison to the per-datum rank implication, reading Gromov and Weiss as its monomial case.
  linear-sofic-surjunctivity-is-a-rank-implication-per-datum: that is the implication over all invertible tuples, equivalent to the linear sofic rung; this is the same implication restricted to monomial tuples, where it holds unconditionally.
artifacts:
  - research/artifacts/linear-sofic-rung-rank-implication-2026-09-12.md
---

**ESTABLISHED** by `gromov-weiss-monomial-rank-implication-proof`.

Let `F` be a finite field and `D` a strict datum. Some reverse word `w` in `W_r(D)` has this property: for every
`eps > 0` there is `delta > 0` such that every tuple of monomial matrices `rho: F(D) -> Mon_n(F)` whose forward
relators have rank at most `delta n` satisfies `rk(rho(w) - 1) <= eps n`.

**Consequences.**
- **The rung, read against this.** `linear-sofic-groups-are-surjunctive` over `F_p` is exactly the extension, for
  every strict datum, of this monomial implication to all invertible tuples, possibly with another reverse word
  (`linear-sofic-surjunctivity-is-a-rank-implication-per-datum`).
- **Near-monomial tuples.** The implication transfers to tuples within rank `theta n` of monomial ones,
  generator by generator, with constants shifted by `4 theta`. A witness to failure of the rung must stay far from
  monomial tuples.

## Attempts

Established; artifact Section 2.
