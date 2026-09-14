---
rg: 2
id: separated-pairing-families-admit-noisy-decoders
kind: claim
title: A separated pairing family can be decoded from one noisy pull-back table with error exponentially small in N
distinct_from:
  noisy-affine-direction-decoding-over-cyclic-alphabets: that is the decoder for the affine family F_lin; this is the agreement-score decoder for any delta_0-separated family of pairings, proved with McDiarmid's inequality.
artifacts:
  - research/artifacts/unique-games-pairing-entropy-obstruction-2026-09-11.md
---

**ESTABLISHED.** Let `P` be a family of perfect pairings of `[N]` in which any two
distinct members share at most a `1 - delta_0` fraction of their pairs. Let
`m >= 2` and `0 < rho < 1`. For `pi in P`, let `A` be uniform on
`pi`-pair-constant vectors in `Z_m^N` and `X = K_rho(A)`, with coordinatewise
retention probability `rho`. Let `jhat(X)` be the least maximizer over
`sigma in P` of the agreement score

```text
S_sigma(X) = (2/N) sum_({x,y} in pairs(sigma)) 1[X_x = X_y].
```

Then `jhat(X + t 1) = jhat(X)` for every `t`, and

```text
Pr[jhat(X) != pi] <= |P| exp(-N rho^4 delta_0^2 / 96).
```

The means are `1/m + (1-1/m) rho^2 ov(sigma,pi)`, so separation gives a margin of
`(1-1/m) rho^2 delta_0 / 2`. McDiarmid's inequality over the `N/2` pair symbols
and `N` noise variables has total squared differences `12/N`.
