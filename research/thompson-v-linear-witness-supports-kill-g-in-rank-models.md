---
rg: 2
id: thompson-v-linear-witness-supports-kill-g-in-rank-models
kind: claim
title: Witnesses for the Thompson V linear targets generate subgroups in which every rank model kills the averaged element
distinct_from:
  ternary-corner-witnesses-need-non-linear-sofic-support: that is the support filter for the anti-central corner of the ternary Leavitt unit group algebra; this is the filter for the V-internal swap and order-three targets in both characteristics, and adds the finite-residual and residually-finite exclusions.
  anti-central-rank-models-kill-ternary-corner-witnesses: that needs the central involution and the pair w, d inside the ternary Leavitt unit group; this lives inside V, which contains no central involution.
artifacts:
  - research/artifacts/thompson-v-rank-support-and-kernel-transfer-2026-09-12.md
---

Let `g = w` and `p = 3` (target `thompson-v-ternary-swap-idempotent-is-full`), or `g = h` and
`p = 2` (target `thompson-v-order-three-averaging-idempotent-is-full`). If `b, c` witness the
target, put `H = <g, supp b, supp c> <= V`. Then `g` lies in the kernel of every homomorphism from
`H` into a characteristic-`p` rank target. Consequences:
- `g` lies in the finite residual of `H`;
- every characteristic-`p` representation of `H` kills `g`;
- `H` is not residually finite, LEF, sofic or `F_p`-linear sofic;
- no witness is supported, together with `g`, in a finite, locally finite, residually finite,
  amenable or linear subgroup of `V`.

Both `w` and `h` lie in Thompson's `T`, which is simple, so `T`-internal witnesses pass the filter.

Proof: Section 2 of the artifact, route `thompson-v-witness-support-rank-model-proof`.
