---
rg: 2
id: v-excludes-bs-1-n-from-hyperbolic-points
kind: route
title: Roots of an element fix its hyperbolic fixed points after a bounded power, so the slope is infinitely divisible
target: bs-1-n-does-not-embed-in-thompson-v
requires:
  - infinite-order-elements-of-v-have-hyperbolic-periodic-points
artifacts:
  - research/artifacts/zp-pl-interval-subgroup-obstructions-2026-09-13-part3.md
---

Full derivation in the artifact: Lemma V-A and §N2-V. Summary:

- If `a ≠ 1` has roots `b_j` with `b_j^{n^j} = a`, then `a` has infinite order, and some
  `a^k` has a finite nonempty set `P` of hyperbolic fixed points.
- Each root commutes with `a^k`, so it permutes `P`, and `b_j^r` fixes `p` in `P` for
  `r = |P|!`.
- The slope homomorphism at `p` gives `r·log_2(a^k)'(p) = k·n^j·log_2(b_j^r)'(p)` for
  all `j`. That is impossible, since `log_2(a^k)'(p) ≠ 0`.
