---
rg: 2
id: binary-cyclic-corner-from-no-weakly-finite-complement-image
kind: route
title: With no weakly finite image the complement corner fails the rank condition, so the binary cyclic corner is full
target: binary-cyclic-averaging-idempotent-is-full-on-leavitt-units
requires: [binary-complement-corner-has-no-weakly-finite-image, rank-condition-rings-have-weakly-finite-images, binary-cyclic-corner-full-iff-complement-corner-has-no-state]
artifacts:
  - research/artifacts/binary-weakly-finite-representations-2026-09-12.md
---

Artifact Theorem W, (b) => (a).
1. By the first requirement, `T = f F_2[R^x] f` has no nonzero weakly finite image.
2. By `rank-condition-rings-have-weakly-finite-images`, applied to the unital ring `T`, the corner `T` fails
   the rank condition.
3. By `binary-cyclic-corner-full-iff-complement-corner-has-no-state` (6 => 1), `c e b = 1` is solvable.

**Nothing is lost.** The first requirement is also necessary for the target (artifact Theorem W, (a) => (c)
=> (b), elementary). So this route turns the binary corner into a statement about weakly finite rings, with
no states and no rank functions.

*Verification by `w4-vf-linear-b` (2026-09-12), Section 35 of `research/artifacts/gk-vf-linear-b-verification-2026-09-12.md`: PASS as an implication. Chain checked: Theorem C (Section 29.4), then Theorem B 6 ⇒ 1 (Section 32.3). The converse (a) ⇒ (c) ⇒ (b) is elementary and was also checked.*

*Spot-check by `w6-vf-chain` (2026-09-12), Section 2 of `research/artifacts/gk-vf-chain-verification-2026-09-12.md`: PASS as an implication. Re-checked the chain Theorem C, then Theorem B 6 ⇒ 1. The first requirement also makes `F_2[R^x]` not stably finite directly: `T` is nonzero and then not weakly finite, and a one-sided pair over `T` pads with `1 - f`.*
