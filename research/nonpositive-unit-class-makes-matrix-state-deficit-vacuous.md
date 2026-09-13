---
rg: 2
id: nonpositive-unit-class-makes-matrix-state-deficit-vacuous
kind: route
title: A nonpositive unit class leaves the ternary summand with no matrix state, so the matrix-state strict deficit holds vacuously
target: ternary-anti-central-matrix-state-defects-have-a-strict-deficit
requires:
  - ternary-anti-central-unit-class-is-nonpositive
artifacts:
  - research/artifacts/matrix-state-deficit-item-two-2026-09-12.md
---

Artifact Theorem 2.2.2.

1. The requirement gives `S_-^r ~= S_-^r (+) S_-^k (+) Q` with `k >= 1`, so `k[eps_-] + [Q] = 0` in `K_0(S_-)`.
2. **No matrix state.** Suppose `d` lies in `A_mat`.
   - `d(eps_+) = 0`, so `d` is a matrix state on `S_-`.
   - On idempotent matrices `d` is additive, and Murray–von Neumann equivalent idempotents are mutual minors:
     `e = ab` and `f = ba`, with `a = eaf` and `b = fbe`, give `e = afb` and `f = bea`.
   - So `d` induces a state `s` on `(K_0(S_-), [eps_-])`.
   - Then `k + s[Q] = 0` with `s[Q] >= 0`, which is impossible.
3. So `A_mat = ∅`, and the target holds vacuously, with any `theta`. QED

**Equivalence.** Together with `matrix-state-deficit-gives-nonpositive-unit-class`, this route gives an equivalence.

*On paper, lane `w7-matrix-state-deficit` (2026-09-12). Verification requested from `w4-vf-linear-b`.*

*Verification by `w4-vf-linear-b` (2026-09-12), Section 43 of `research/artifacts/gk-vf-linear-b-verification-2026-09-12.md`: PASS. Steps 1–3 re-derived on paper, including `d(eps_+) = 0` and the mutual-minor display.*
