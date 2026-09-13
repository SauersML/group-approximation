---
rg: 2
id: vd-standard-square-words-have-polynomial-area
kind: claim
title: The standard square words of V_d have polynomially bounded area
distinct_from:
  vd-dehn-bounded-by-standard-square-word-area: that reduces the Dehn function of V_d to the area A_d(n) of these words; this asserts that A_d(n) is polynomially bounded.
---

**OPEN.** For every `d >= 2`, with the standard square words `Q_n` of
`vd-dehn-bounded-by-standard-square-word-area`, some polynomial `P_d` satisfies
`A_d(n) <= P_d(n)`.

**Equivalent working form.** A square word commutes two splits of distinct
standard pieces, conjugated by leaf permutations of standard trees. It
therefore suffices that, over some finite presentation, two families have area
`poly(n)`:

1. the Coxeter relators of `S_n` acting on the leaves of the standard `n`-leaf
   tree;
2. the intertwining relators `split_j ∘ τ = τ^split ∘ split_(τ^(-1)(j))`.

For `d = 2` these are the π-word lemmas of Lorrain arXiv:2608.03813v2 §3–§4
(costs `O(n^2)` to `O(n^6)`; see
`research/artifacts/zp-thompson-v-dehn-function-2026-09-13.md` §2).

## Attempts

- **Cone transport (lane solve-vd-dehn-filling, 2026-09-13).** Relators
  supported in one cone of depth `m` are conjugates, by powers of the comb shift
  `x_0`, of relators supported in a standard cone, so they have bounded area.
  Coxeter relators `(π_i π_(i+1))^3` defined by `x_0`-conjugation are exact
  conjugates of `(π_1 π_2)^3`, so their area is `O(1)`. The open part is far
  commutation `[π_1, π_m]`: the `x_0`-conjugator does not fix the support of
  `π_1`, so one needs a conjugator that fixes it, such as `x_2` for the right
  comb, together with polynomial-cost conversion between the two definitions of
  `π_m`. This is the `d`-ary analogue of Lorrain's §3.3.
