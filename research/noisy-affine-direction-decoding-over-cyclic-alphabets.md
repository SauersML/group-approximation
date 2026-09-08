---
rg: 2
id: noisy-affine-direction-decoding-over-cyclic-alphabets
kind: claim
title: Equality scores recover a noisy affine pairing direction over every cyclic alphabet
artifacts:
  - research/artifacts/unique-games-affine-test-soundness-2026-09-07.md
  - scripts/check_unique_games_affine_soundness.py
  - research/artifacts/unique-games-affine-test-replay-2026-09-07.json
---

Let `F=GF(4^r)`, `N=|F|`, `m>=2`, and `0<rho<1`. Choose a
uniform `Z_m` vector constant on the pairs `{x,x+b}` for a fixed
nonzero `b`, independently across pairs. Apply ambient noise which
retains each coordinate with probability `rho` and otherwise resamples
it uniformly, obtaining `Y`.

Let `bhat(Y)` maximize `sum_x 1_(Y_x=Y_(x+c))` over nonzero `c`,
with ties broken by a fixed ordering of the directions. Then

```text
Pr[bhat(Y)!=b] <= (N-1)exp(-N rho^4/32).
```

The bound holds for each planted direction and uniformly in `m>=2`.
The decoder is invariant under adding a constant to all input symbols.
For any coordinate selectors `q_(u,c)`, the functions
`F_u(Y)=Y_(q_(u,bhat(Y)))` are consequently folded.

This is the arbitrary-output-alphabet decoder needed by
`affine-long-code-test-has-no-uniform-soundness`. The earlier Boolean
counterexample additionally proves influence and hitting-set statements;
those are separate conclusions, not part of this claim.
