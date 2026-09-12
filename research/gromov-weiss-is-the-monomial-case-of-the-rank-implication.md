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
  - research/artifacts/gk-vf-positive-b-verification-2026-09-12.md
---

**ESTABLISHED** by `gromov-weiss-monomial-rank-implication-proof`. w4-vf-positive-b re-derived it
independently and it passed (Section 4 of its verification artifact).

Let `F` be a finite field and `D` a strict datum. Some reverse word `w_mon` in `W_r(D)` has this property: for every
`eps > 0` there is `delta_mon(eps) > 0` such that every tuple of monomial matrices `rho: F(D) -> Mon_n(F)` whose
forward relators have rank at most `delta_mon(eps) n` satisfies `rk(rho(w_mon) - 1) <= eps n`.

## Consequences

- **The rung, read against this.** `linear-sofic-groups-are-surjunctive` over `F_p` says exactly this: for every
  strict datum, the implication extends from monomial tuples to all invertible tuples, possibly with another
  reverse word (`linear-sofic-surjunctivity-is-a-rank-implication-per-datum`).
- **Near-monomial tuples.** For `eps > 4 theta` put `delta = delta_mon(eps - 4 theta) - 4 theta`, and suppose
  `delta > 0`.
  - Take a tuple within rank `theta n` of a monomial tuple, generator by generator, whose forward relators have
    rank at most `delta n`. Then it satisfies `rk(rho(w_mon) - 1) <= eps n`.
  - Word ranks are invariant under simultaneous conjugation, so the same holds near every conjugate of a monomial
    tuple.
- **So.** Tuples witnessing a failure of the rung for `D` in particular fail the implication at `w_mon`, with some
  margin `eps`. At small forward relator rank they stay at rank distance at least `theta n` from the whole
  conjugation orbit of monomial tuples, for every `theta < eps/4` with `delta_mon(eps - 4 theta) > 4 theta`.

## Attempts

Established; artifact Section 2.
