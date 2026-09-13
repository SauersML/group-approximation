---
rg: 2
id: matrix-state-deficit-gives-nonpositive-unit-class
kind: route
title: A strict deficit over anti-central matrix states fails at a minimizer, so the ternary summand has no matrix state and its unit class is nonpositive
target: ternary-anti-central-unit-class-is-nonpositive
requires:
  - ternary-anti-central-matrix-state-defects-have-a-strict-deficit
  - two-root-gate-lower-bounds-hold-for-matrix-states
  - sylvester-rank-functions-iff-no-triangular-certificate
  - anti-central-state-obstruction-equals-stable-finiteness
artifacts:
  - research/artifacts/matrix-state-deficit-item-two-2026-09-12.md
---

Artifact Lemma 2.1 and Theorem 2.2.2. This is the Consequence paragraph of
`two-root-gate-lower-bounds-hold-for-matrix-states`, written as a route.

1. **Minimizer.** Suppose `A_mat` is nonempty. By item 3 of the second requirement, `c_3^mat > 0` is attained at
   some `d_0`.
2. **Compression.**
   - Take disjoint nonempty proper cylinders `A`, `B` with proper union.
   - Item 1 of the first requirement gives `d_0(D_A D_B) > 0`.
   - So `h = d_0(Q_B D_A) > 0`, by item 3 of the second requirement (Theorem 3.1.4 of the characteristic-three
     artifact).
   - Then `d_0'(X) = d_0(F_3[iota_B](X) Q_B D_A)/h` is a matrix state with `d_0'(eps_-) = 1`.
3. **Contradiction.** By minimality `d_0'(D) >= d_0(D)`. Item 2 gives `d_0'(D) <= theta d_0(D) < d_0(D)`.
4. **Conclusion.**
   - So `A_mat = ∅`. Every matrix state on `S_-` pulls back into `A_mat`, so `S_-` has none.
   - By item 2 of `sylvester-rank-functions-iff-no-triangular-certificate`, `S_-` fails the rank condition and
     `(K_0(S_-), [eps_-])` has no state.
   - Part 2 of `anti-central-state-obstruction-equals-stable-finiteness` gives `k[eps_-] <= 0` for some `k >= 1`,
     which is the target. QED

**Equivalence.** Together with `nonpositive-unit-class-makes-matrix-state-deficit-vacuous`, this route gives an
equivalence. So the first requirement is a restatement of the target, not a weakening.

*On paper, lane `w7-matrix-state-deficit` (2026-09-12). Verification requested from `w4-vf-linear-b`.*

*Verification by `w4-vf-linear-b` (2026-09-12), Section 43 of `research/artifacts/gk-vf-linear-b-verification-2026-09-12.md`: PASS. Steps 1–4 re-derived on paper; the item citations checked against the required nodes on main. Decision-relevant: together with its converse route, this makes the deficit claim a restatement of the target.*
