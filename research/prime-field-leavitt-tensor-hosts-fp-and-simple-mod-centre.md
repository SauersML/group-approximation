---
rg: 2
id: prime-field-leavitt-tensor-hosts-fp-and-simple-mod-centre
kind: claim
title: Over every prime field, B ⊗ L_p has finitely presented unit group, simple modulo scalars, once K_1 and K_2 vanish
distinct_from:
  leavitt-tensor-hosts-acyclic-steinberg-and-fp: that is the characteristic-two host theorem, where Khanh's criteria apply as written; this covers every prime p, which needs Quillen's weight count at odd p and a signed Steinberg comparison with a central correction.
  central-simple-leavitt-tensor-unit-groups-are-simple: that proves simplicity when the only central unit is 1; this proves simplicity modulo the scalars F_p^x, which are central for odd p.
  odd-leavitt-steinberg-reflection-prerequisites: that audits odd-characteristic reflection words and connector lifts inside St_r(L_p); this proves the Steinberg map is an isomorphism over B ⊗ L_p through Brown's presentation with signed transporters.
artifacts:
  - research/artifacts/boone-higman-prime-field-leavitt-hosts-2026-09-12.md
---

**ESTABLISHED (conditional on the imported criteria of Khanh
arXiv:2609.08428v1).** Let `p` be a prime, `L_p = L_(F_p)(1,2)`, `B` a simple
unital `F_p`-algebra, and `R = B ⊗ L_p`.

1. If `K_i(R) = 0` for `1 <= i <= N`, then `H_n(GL_r(R); Z) = 0` for
   `1 <= n <= N` and every `r`.
2. If `K_1(R) = K_2(R) = 0`, then `GL_m(R) = E_m(R)` for `m >= 2` and
   `St_r(R) -> GL_r(R)` is an isomorphism for `r >= 3`.
3. If in addition `B` is a finitely presented ring, `R^x` is finitely presented.
4. If `B` is central simple:
   - `E_n(R)` modulo its scalar centre is simple for `n >= 3`;
   - under the hypothesis of (2), `R^x / F_p^x` is simple.

There are two new ingredients.
- **Quillen's count at odd `p`.** Weights on `H*(V; F_p)` in degrees `0 < j < m`
  are nontrivial characters of `F_(p^m)^x`.
- **Steinberg comparison in every characteristic.** Signed transporters
  `W = X_12(-1) X_21(1) X_12(-1)`, and `W_23` likewise. The braid relation holds
  after multiplying by the central element
  `z = (W_23 W W_23)(W W_23 W)^-1`.

DERIVATION
prime-field-leavitt-tensor-hosts-proof
