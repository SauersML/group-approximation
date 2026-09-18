---
rg: 2
id: design-test-universality-forces-surjunctive-groups-sofic-proof
kind: route
title: Normal Dirac points have transitive shapes, so designs are automata over the quotient and the error densities are zero or one
target: design-test-universality-forces-surjunctive-groups-sofic
requires:
  - co-sofic-free-group-irs-carry-no-strict-design
  - atomic-irs-strict-designs-are-nonsurjunctive-quotients
artifacts:
  - research/artifacts/design-subgroup-tests-2026-09-17.md
  - research/artifacts/irs-surjunctivity-heretic-2026-09-17.md
---

Complete direct proof: artifact Section 4.
- It uses the rank-corrected co-sofic inequality (`co-sofic-free-group-irs-carry-no-strict-design`) and the
  atomic case (`atomic-irs-strict-designs-are-nonsurjunctive-quotients`), both ESTABLISHED.
- The universality corollary also cites Gromov-Weiss (sofic groups are surjunctive), but only to state the
  equivalence.

1. **Transitivity.** Left multiplication makes all rooted shapes of `X_N` equal. So a design is a pair of automata
   over `G`, and `eps` and `delta` each lie in `{0, 1}`.
2. **(a).**
   - If `G` is surjunctive: `eps = 0` forces bijectivity, so `delta = 0`; and `eps = 1` gives
     `delta <= 1 <= C_D`.
   - If `G` is not surjunctive: an injective non-surjective automaton, with a cellular left inverse lifted to
     words, gives `eps = 0 < delta = 1`.
3. **(b).**
   - Lifts `w_g` of the elements of `G` give a sofic approximation `v -> v.w_g^-1` from finite graphs converging to
     `delta_N`.
   - Conversely, sofic approximations define finite `F_r`-actions converging to `delta_N`.
4. **Compiler.** Take `F = { some relator not in H, or some w in W in H }`.
   - Relators holding at most points imply that each fixed element of `N` holds at most points, by a union bound
     over its conjugate factorization.
   - So a finite-graph value tending to `0` would make `delta_N` co-sofic, contradicting (b).
   - `delta_N(F) = 0`. The compiled design is strict for `delta_N`, and Theorem 3.1 of the heretic artifact makes
     `G` non-surjunctive.
