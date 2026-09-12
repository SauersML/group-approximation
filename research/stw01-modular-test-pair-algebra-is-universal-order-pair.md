---
rg: 2
id: stw01-modular-test-pair-algebra-is-universal-order-pair
kind: claim
title: The modular test pair generates the universal C*-algebra of one order pair 0 <= k <= h - h^2
distinct_from:
  stw01-modular-test-pair-generates-non-exact-algebra: that shows C*(h, k) surjects onto Q and so is not exact; this identifies C*(1, h, k) exactly as the universal unital C*-algebra of the relations 0 <= h <= 1, 0 <= k <= h - h^2.
artifacts:
  - research/artifacts/stw01-universal-order-pair-test-2026-09-12.md
---

In `Q = C^3 * C^2 = C*(PSL_2(Z))` let `h = e_1 p e_1` and `k = e_1 p e_2 p e_1`. Let `U` be
the universal unital C*-algebra of two elements `h_0, k_0` subject to

```text
0 <= h_0 <= 1,        0 <= k_0 <= h_0 - h_0^2.                               (OP)
```

The pair `(h, k)` satisfies (OP), because `h - h^2 = k + e_1 p e_3 p e_1`. The unital
*-homomorphism `U -> Q` with `h_0 -> h` and `k_0 -> k` is injective, so

```text
C*(1, h, k) ~= U.
```

**Consequence.** The single-pair test `stw01-modular-single-pair-quasitrace-additivity`
uses no structure of `C*(PSL_2(Z))` beyond this one order relation. Kaplansky's problem is
equivalent to additivity on the universal order pair,
`stw01-universal-order-pair-quasitrace-additivity`.

`U` also surjects onto `Q`. Send `h_0` to `sum_i lambda_i e_i` with distinct
`lambda_i in (0, 1)`, and `k_0` to `m p` with `m = min_i lambda_i (1 - lambda_i)`.

Proof: `stw01-modular-test-pair-algebra-is-universal-order-pair-proof`, and Section 1 of
`research/artifacts/stw01-universal-order-pair-test-2026-09-12.md`.
