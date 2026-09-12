---
rg: 2
id: odd-measure-nonamenable-thompson-support-proof
kind: route
title: A locally finite reflection kernel over an amenable projection makes the support group sofic, so its group algebra is directly finite
target: odd-measure-corner-witnesses-need-nonamenable-thompson-support
requires:
  - sofic-kernel-amenable-quotient-permanence
  - sofic-implies-linear-sofic-over-every-field
  - linear-sofic-group-algebra-is-stably-finite
  - signed-thompson-algebra-is-odd-measure-crossed-product
  - hadamard-unit-conjugates-swap-idempotent-to-cylinder
artifacts:
  - research/artifacts/gk-vf-linear-verification-2026-09-12.md
  - research/artifacts/ternary-lift-signed-thompson-crossed-product-2026-09-12.md
---

## Why sufficient

Suppose `K` is amenable.

* **The kernel is sofic.** `L cap E` is a subgroup of `E ~= C(X, F_2)`, an elementary abelian
  `2`-group, so it is locally finite. A locally finite group is sofic: the finite subgroup generated
  by a finite set acts on itself by left translation, exactly multiplicatively and freely.
* **`L` is sofic.** `L cap E` is normal in `L` with `L/(L cap E) ~= K`, so `L` is sofic by
  `sofic-kernel-amenable-quotient-permanence`.
* **Directly finite.** By `sofic-implies-linear-sofic-over-every-field`, `L` is `F_3`-linear sofic.
  By `linear-sofic-group-algebra-is-stably-finite`, `F_3[L]` is directly finite.
* **The corner lives in `F_3[L]`.** Since `z` and `tau_[0]` lie in `L`, the elements `b'`, `c'`,
  `q_[0]` and `q_[1]` lie in `eps_- F_3[L]`, and the idempotents `eps_(+-)` are central
  (`signed-thompson-algebra-is-odd-measure-crossed-product`).
* **Contradiction.** Put `x = q_[0] b' + eps_+` and `y = c' q_[0] + eps_+`.
  * The cross terms vanish, so `y x = c' q_[0] b' + eps_+ = 1`.
  * Direct finiteness gives `x y = q_[0] b' c' q_[0] + eps_+ = 1`, that is
    `q_[0] b' c' q_[0] = eps_-`.
  * Multiply on the left by `q_[1]`. By `hadamard-unit-conjugates-swap-idempotent-to-cylinder`,
    `q_[1] q_[0] = 0`, so `0 = q_[1] eps_- = q_[1]`.
  * But `q_[1] != 0`: `1`, `[tau_[0]]`, `[z]` and `[z tau_[0]]` are distinct basis elements.

So `K` is nonamenable. Proposition 8 of the artifact.

*Verified independently by `gk-vf-linear` (2026-09-12): Section 30 of `research/artifacts/gk-vf-linear-verification-2026-09-12.md`.*
