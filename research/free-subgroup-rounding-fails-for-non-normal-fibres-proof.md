---
rg: 2
id: free-subgroup-rounding-fails-for-non-normal-fibres-proof
kind: route
title: A coordinate hyperplane is a permutable certificate and labeling, while free subgroups must omit all N coordinate flips
target: free-subgroup-rounding-fails-for-non-normal-fibres
requires: [galois-games-round-through-free-subgroups]
artifacts:
  - research/artifacts/ugc-rounding-normal-fibres-2026-09-13.md
---

Complete proof: Proposition 13 of the artifact.

* **Exponent.** `(b,t)^2 = (b + t.b, 0)` lies in the elementary abelian `B`,
  so every element has order dividing `4`.
* **The measure.** `mu_delta(b) = delta^|b| (1 - delta)^(N - |b|)` on `B` is
  symmetric (`b = b^-1`). It is conjugation-invariant, because `B` is abelian
  and translations preserve Hamming weight.
* **Lower bounds.** `L = { b_0 = 0 }` has `L cap K = {e}` and `KL = B`, a
  subgroup, and `mu_delta(L) = 1 - delta`. Part 5 of the required claim (subgroup
  certificates and permutable rounding) gives `SDP >= 1 - delta` and
  `val >= 1 - delta`.
* **Free subgroups.** `x e_0 x^-1 = e_(t)` for `x = (b,t)`, so the conjugates of
  `K` are all `<e_j>`. By the duality in part 1 of the required claim, `H` is
  free iff it contains no `e_j`. Hence
  `mu(G \ H) >= sum_j mu(e_j) = N delta (1 - delta)^(N-1)`.
* **No constant.** With `delta = N^-2`, Bernoulli gives
  `N (1 - N^-2)^(N-1) >= N - (N-1)/N > N - 1`, while `eps log_2 k = N^-2`.
