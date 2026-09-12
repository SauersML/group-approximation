---
rg: 2
id: ternary-anti-central-kernel-klein-idempotents-proof
kind: route
title: Sign patterns on level-two cylinders give commuting involutions whose averaging idempotent evaluates to zero
target: ternary-anti-central-kernel-has-klein-idempotents
requires: []
artifacts:
  - research/artifacts/gk-vf-linear-verification-2026-09-12.md
  - research/artifacts/ternary-anti-central-kernel-normal-forms-2026-09-12.md
---

Section 1 of the artifact.
* The `h_i` are `+-1` combinations of the four orthogonal cylinder idempotents, so they are
  commuting involutions. No product of them has the all-minus pattern `z`.
* `E = [1]+[h1]+[h2]+[h1h2]` satisfies `E^2 = 4E = E`, and
  `pi(E) = (1+h1)(1+h2) = 4(q_00+q_01) q_10 = 0`.
* `q = 2(1-[z])E` has coefficient `2` on `[1]` inside the group algebra of `H x <z>`.

*Verified independently by `gk-vf-linear` (2026-09-12): Section 8 of `research/artifacts/gk-vf-linear-verification-2026-09-12.md`.*
