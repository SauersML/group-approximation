---
rg: 2
id: stw01-order-pair-defects-rescale-generic-defects
kind: claim
title: Every positive-pair quasitrace defect is an order-pair defect after an affine rescaling
distinct_from:
  stw01-universal-order-pair-quasitrace-additivity: that asks whether every quasitrace on the universal order-pair algebra adds the pair; this proves the order relation restricts nothing, because every positive pair in every unital algebra rescales into an order pair carrying a fixed multiple of its defect.
  stw01-modular-test-pair-algebra-is-universal-order-pair: that identifies C*(1, h, k) inside C*(PSL_2(Z)) with the universal order-pair algebra; this is an elementary rescaling of arbitrary positive pairs into order pairs and uses no group algebra, dilation or AW*-factor.
artifacts:
  - research/artifacts/stw01-order-pair-rescaling-2026-09-12.md
---

Let `A` be a unital C*-algebra and `sigma` a bounded 2-quasitrace on `A`. For
`a, b in A_+` write `D(a, b) = sigma(a + b) - sigma(a) - sigma(b)`. Let `x, y in A_+` with
`||x||, ||y|| <= 1`, let `0 < eps <= 1/5` and `0 <= s <= 1/4 - eps - eps^2`, and put

```text
h = (1/2) 1 + eps x,        k = s 1 + eps y.
```

Then:

1. `sp(h) ⊂ [1/2, 1/2 + eps]` and `0 <= k <= h - h^2`. So `(h, k)` satisfies (OP) of
   `stw01-universal-order-pair-quasitrace-additivity`, and there is a unital
   *-homomorphism `psi : U -> A` with `h_0 -> h`, `k_0 -> k`.
2. `D(h, k) = eps D(x, y)`.
3. With `s = 1/4 - eps - eps^2`, the pair is squeezed:
   `(1 - 4 eps - 4 eps^2)(h - h^2) <= k <= h - h^2`.

The proof uses only linearity of `sigma` on commutative C*-subalgebras. Proof:
`stw01-order-pair-defects-rescale-generic-defects-proof`, and Section 1 of
`research/artifacts/stw01-order-pair-rescaling-2026-09-12.md`.

**Consequence.** Additivity on the universal order pair implies Problem I directly
(`stw01-problem-i-via-universal-order-pair`): a non-trace quasitrace is non-additive on
some positive pair, and item 1 pulls it back to `U` with defect `eps D(x, y) != 0`. No
AW*-factor, three-block dilation or intermediate-value tuning is needed.

**What it rules out.** The order relation carries no leverage. Non-additive witnesses
on `U` exist with `sp(h_0)` inside a window of width `eps` at `1/2`, and with `k_0` squeezed
to within `O(eps)` of `h_0 - h_0^2`. So an argument that uses the spectrum of `h_0` near `0`
or `1`, the size of `h_0 - h_0^2`, or the room `h_0 - h_0^2 - k_0` cannot reach every witness.
Any proof of `stw01-universal-order-pair-quasitrace-additivity` is a proof of additivity
for arbitrary positive pairs.

**Credit.** The rescaling is elementary and very likely folklore. No novelty is claimed.
