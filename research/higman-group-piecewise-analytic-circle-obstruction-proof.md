---
rg: 2
id: higman-group-piecewise-analytic-circle-obstruction-proof
kind: route
title: Each generator is conjugate to its square by the previous one; a gap end of g_(i+1) is fixed by a power of g_i with derivative different from 1, while g_i is tangent to the identity at its fixed points
target: higman-group-embeds-in-no-piecewise-analytic-circle-group
requires:
  - piecewise-analytic-circle-square-conjugate-has-parabolic-ends
---

Write "the lemma" for `piecewise-analytic-circle-square-conjugate-has-parabolic-ends`,
and `G_i` for the image of `g_i`.

**Item 1 (orientation).** For the orientation character `ε`,
`ε(g_(i+1)) = ε(g_i g_(i+1) g_i^-1) = ε(g_(i+1))^2 = 1`. So every `G_i` lies in
`PA_+(S^1)`, and `G_i G_(i+1) G_i^-1 = G_(i+1)^2` for all `i ∈ Z/4`.

**Item 2 (one generator).** Suppose `G_(i+1) ≠ 1`.
- **A power of `G_i` is hyperbolic at a gap end.** By the lemma with `n = 2`,
  `G_(i+1)` has a fixed point. Take a gap `J` with endpoint `p`. Lemma Items 1
  and 3, for `(g,h) = (G_(i+1), G_i)`, give `N ≥ 1` with `G_i^N(p) = p` and
  one-sided derivative `2^(-N/m) ≠ 1` at `p` from `J`.
- **`G_i` fixes `p` and is tangent to the identity there.** The lemma for
  `(g,h) = (G_i, G_(i-1))` shows that `G_i` has a fixed point, so its periodic
  point `p` is fixed. Lemma Item 2 gives one-sided derivatives `1` at `p`.
- **The contradiction.** `G_i` preserves the `J` side of `p`, so the chain rule
  gives derivative `1` for `G_i^N` there, which is impossible.

Hence `G_(i+1) = 1`.

**Item 3 (conclusion).** Item 2 holds for every `i ∈ Z/4`, so every generator
maps to `1`.
