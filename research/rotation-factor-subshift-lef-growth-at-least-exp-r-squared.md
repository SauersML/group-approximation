---
rg: 2
id: rotation-factor-subshift-lef-growth-at-least-exp-r-squared
kind: claim
title: Subshifts with an irrational rotation factor and a letter sandwiched by an arc have LEF growth at least exp(c r²); codings of rotations by intervals have exactly exp(Θ(r²))
---

**Statement.** Assume hypothesis (R) of `rotation-factor-subshifts-have-linear-cost-towers`. Let n_0 be least with |η_{n_0}| < min(|I|, 1 − |I|), and put m_0 = ⌈q_{n_0}/2⌉. Then for every r ≥ 100 + 2400·m_0,

`L_X(r) ≥ 2^{18((r − 2500)/2400)²}`,

where L_X is the LEF growth of EL_3(LC(X,F_2)⋊Z).

Adding `rauzy-walk-bounds-lef-growth-by-special-factors` gives L_X ≃ exp(r²) whenever s_X(n) = p_X(n+1) − p_X(n) is bounded. This includes every coding of an irrational rotation by finitely many intervals, given Cassaigne's theorem (recalled).

**Status: established** by `rotation-factor-subshift-lef-growth-at-least-exp-r-squared-proof`. UNREVIEWED; queued with sk-referee-2.
