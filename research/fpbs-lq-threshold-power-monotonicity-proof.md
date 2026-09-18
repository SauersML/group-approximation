---
rg: 2
id: fpbs-lq-threshold-power-monotonicity-proof
kind: route
title: Prove thinning by convexity of an l^r norm and edge induction, then compare Z_q at p with Z_q' at p^(q/q')
target: fpbs-lq-threshold-power-monotonicity
requires: []
artifacts:
  - research/artifacts/fpbs/docs/lq-threshold-power-monotonicity-2026-09-17.md
  - experiments/lq-threshold-power-2026-09-17/check_thinning.py
---

The complete written proof is in the artifact.

**Imports.** Both are quoted there in Lemma 3.3.

- [DT] arXiv:1502.03050v3, lines 314–322 and 349–354 of
  `sharpnessPercoIsing-H.tex`, as quoted in
  `fpbs-l2-gap-class-closed-under-local-limits-proof`.
- BK (Grimmett, *Percolation*, 2nd ed., Section 2.3).

**Steps.**

1. **(2.1)** `(p+(1-p)x)^g <= p^g + (1-p^g)x^g`. The left side is the
   `l^r` norm of an affine map of `s = p^g`, with `r = 1/g`, so it is convex
   in `s`. The right side is its chord.
2. **Lemma 2.1.** `P_(p^g)(A) >= P_p(A)^g` for finite increasing `A`, by
   conditioning on one edge and applying (2.1) with `x = a_0/a_1`.
3. **Corollary 2.2.** The same holds for `tau`, by exhausting with balls.
4. **Theorem 3.1.** For `p > p_q^(q/q')`,
   `Z_(q')(p) >= Z_q(p^(q'/q)) = infinity`.
5. **Lemma 3.3.** `chi_p <= |S|/(1 - varphi_p(S))`, by the first-exit BK
   bound with a finite truncation. So `p_1 = p_c`.
6. **Theorem 3.2.** Two-sided power bounds give continuity. Then `q_0` is
   excluded from the up-set `{p_q > p_c}`. The tree identity is
   `tau = p^|x|`.
7. **Corollaries 4.1, 4.2 and Proposition 5.1.** These are direct
   consequences of steps 4–6.
