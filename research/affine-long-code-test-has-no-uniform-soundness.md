---
rg: 2
id: affine-long-code-test-has-no-uniform-soundness
kind: claim
title: The folded long-code noise test maps explicit low-value affine games to high-value unique games
artifacts:
  - research/artifacts/unique-games-affine-test-soundness-2026-09-07.md
  - scripts/check_unique_games_affine_soundness.py
  - research/artifacts/unique-games-affine-test-replay-2026-09-07.json
---

For the source family `G_N` in `affine-shift-games-have-vanishing-value`,
apply the three-noise folded long-code test `R_(rho,m)` defined exactly
in Section 4 of the artifact (BKM, ITCS 2021, Section 5). For every
`m>=2`, `0<rho<1`, and `N=4^r`, its output has a folded labeling with

```text
val(G_N) <= 2/sqrt(N),
val(R_(rho,m)(G_N))
  >= 1/m+(1-1/m)rho^3-2(N-1)exp(-N rho^4/32).
```

For any `eta,epsilon>0` and `m>=2`, some rational `rho<1` and
sufficiently large `N` give source value at most `eta` and output
value at least `1-epsilon`. The explicit choice `N=16384`,
`rho=99/100` gives source value at most `1/64` and output value
greater than `97/100`, uniformly in `m>=2`.

This rules out uniform soundness for this test on all `F_lin`-rich
inputs. It does not contradict the published theorem, which assumes
uniformity over all perfect pairings, and it does not rule out different
tests or extra restrictions on the input family. UGC and Rich 2-to-1
hardness remain open. No new hardness route is asserted.
