---
rg: 2
id: matrix-state-strict-deficit-restricts-to-rank-functions
kind: route
title: Anti-central Sylvester rank functions are matrix states, so the matrix-state strict deficit gives the Sylvester one with the same factor
target: ternary-anti-central-disjoint-defects-have-a-strict-deficit
requires:
  - ternary-anti-central-matrix-state-defects-have-a-strict-deficit
artifacts:
  - research/artifacts/matrix-state-deficit-item-two-2026-09-12.md
---

Artifact Corollary 2.3.

1. A Sylvester matrix rank function is a matrix state: `N(I_1) = 1`, it is additive on block sums, and
   `N(XMY) <= N(M)` by submultiplicativity. So `A_S ⊆ A_mat`.
2. The compressed function has the same formula in both scopes. So items 1–2 over `A_mat` with a given `theta` give
   items 1–2 over `A_S` with the same `theta`. QED

**Scope.**
- The converse follows from (U1) (`ternary-anti-central-states-give-sylvester-rank-functions`).
- The requirement is equivalent to `ternary-anti-central-unit-class-is-nonpositive`, and the target to
  `sylvester-rank-functions-on-ternary-leavitt-units-kill-minus-one` (artifact Theorem 2.2).
- So this route is the implication from the counterexample to the kill claim, in deficit form.

*On paper, lane `w7-matrix-state-deficit` (2026-09-12). Verification requested from `w4-vf-linear-b`.*

*Verification by `w4-vf-linear-b` (2026-09-12), Section 43 of `research/artifacts/gk-vf-linear-b-verification-2026-09-12.md`: PASS. Steps 1–2 re-derived on paper; the converse checked against the statement of (U1).*
