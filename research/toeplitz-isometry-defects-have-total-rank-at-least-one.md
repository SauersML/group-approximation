---
rg: 2
id: toeplitz-isometry-defects-have-total-rank-at-least-one
kind: claim
title: In every Sylvester matrix rank function the defects of t0 s0 = 1, t1 s1 = 1 and t1 s0 = 0 have total rank at least one
distinct_from:
  leavitt-algebra-has-no-unital-rank-model: that is the qualitative non-embedding of the binary Leavitt algebra into rank ultraproducts, proved through simplicity and direct finiteness; this is the quantitative bound with the sharp constant 1, for every Sylvester matrix rank function on every ring, using three relations and no simplicity.
  rank-four-isometry-relations-give-corner-cuntz-family: that asserts a nonzero two-root defect builds a corner Leavitt family; this is the elementary endpoint showing that a left-invertible element and one nonzero left annihilator in a corner already give the contradiction.
artifacts:
  - research/artifacts/leavitt-ring-rank-approximability-collapse-2026-09-12.md
---

**ESTABLISHED 2026-09-12** by `toeplitz-isometry-defects-total-rank-proof`. Verified independently by
`w4-vf-gate` (PASS, Section 4 of `research/artifacts/gk-vf-gate-verification-2026-09-12.md`, b7cec288d7).

Let `A` be a unital ring with a Sylvester matrix rank function `rk`, let `e` be an idempotent of `A`, and
let `S_0, S_1, T_0, T_1 in eAe`. Then

```text
rk(e) <= rk(e - T_0 S_0) + rk(e - T_1 S_1) + rk(T_1 S_0).
```

This rests on two more basic facts: for `S, T in eAe` and `X in Ae`,

```text
rk(e - ST) = rk(e - TS),        rk(X) <= rk(e - TS) + rk(XS).
```

The constant is sharp: take `A = k`, `S_0 = T_0 = 1` and `S_1 = T_1 = 0`.

**Consequences** (artifact Sections 1–3).
* **No approximate representations.** Let `K, k` be fields, `d >= 2`, and `phi : L_K(1,d) -> M_n(k)` any
  map with `phi(0) = 0` and `phi(1) = 1`. Then `phi` has normalized-rank multiplicativity defect at least
  `1/3` on one of the pairs `(t_0,s_0)`, `(t_1,s_1)`, `(t_1,s_0)`. So the right-hand side of
  `leavitt-unit-linear-soficity-is-ring-rank-approximability` is false.
* **Corners.** In a ring with a faithful Sylvester rank function, such as a rank ultraproduct, no nonzero
  corner `eMe` contains `S, T, X` with `TS = e`, `XS = 0` and `X != 0`. That is all the end of the Plan 1
  assembly needs.
* **Isometries.** They are never approximately proper: `rk(1 - st) = rk(1 - ts)` exactly.

## Attempts

This claim is established; see the proof route. It is an endpoint, not an extraction, so it stops short
of producing `S, T, X`. Getting them from a rank model of `R^x` is the open
`rank-four-isometry-relations-give-corner-cuntz-family` and `el3-rank-models-factor-through-ring-rank-models`.
