---
rg: 2
id: rauzy-walk-bounds-lef-growth-by-special-factors
kind: claim
title: The periodic LEF models of G_X have period at most p(n) + (s(n−1)+1)(p(n−1)−1); bounded special factors give LEF growth at most exp(O(r²))
---

**Statement.** Let X be an infinite minimal subshift, with complexity p_X and s_X(n) = p_X(n+1) − p_X(n). Let N_X(n) be the least length of a cyclic word whose cyclic windows of length n are exactly L_n(X). Then

`N_X(n) ≤ p_X(n) + (s_X(n−1) + 1)(p_X(n−1) − 1)`.

**Consequence.** If s_X ≤ S, then N_X(n) ≤ (S+2)(|A| + Sn). By Theorem A of `subshift-elementary-group-lef-growth-complexity-bounds` (L_X(r) < 2^{9N_X(4r+1)²}), the LEF growth of EL_3(LC(X,F_2)⋊Z) is ≼ exp(r²).

s_X is bounded for linear complexity (Cassaigne; RECALLED, source not re-read). So the bound covers linearly recurrent subshifts and codings of rotations by finitely many intervals.

This improves the Rauzy-walk bound (p_X(n)+1)·p_X(n−1) of Theorem A(d), which only gives exp(O(r⁴)) for linear complexity.

**Status: established** by `rauzy-walk-bounds-lef-growth-by-special-factors-proof`. UNREVIEWED; queued with sk-referee-2.

**Review (sk-verify-7, 2026-09-13, `research/artifacts/sk-review-7-2026-09-13-part3.md`):** PASS: ear-decomposition walk bound re-derived (§6); Corollary U1 is conditional on Cassaigne's theorem (recalled).
