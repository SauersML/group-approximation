---
rg: 2
id: paradox-side-elementary-group-is-finitely-presented
kind: claim
title: Some paradox-side rung EL_n(L_k(1,d)) of the UN ladder is finitely presented, which would complete the coarse separation inside the ladder
distinct_from:
  steinberg-finite-presentation-and-kazhdan-theorem: that gives finite presentation of the Steinberg group St_n(R) and explicitly declines any conclusion about EL_n(R); this asks for the quotient group itself.
artifacts:
  - research/artifacts/un-open-7-coarse-geometry-2026-09-13.md
---

**OPEN.** Is `EL_n(L_k(1,d))` finitely presented for some `n >= 4`, `d >= 2` and some
finite field `k`?

**Why it is worth deciding.** `lef-infinite-simple-groups-are-qi-rigid` separates the
measure side of the ladder from the finitely presented Kazhdan examples of the non-MF
paper by a quasi-isometry invariant. A yes here would upgrade that to a separation
*inside* the ladder: one rung finitely presented, every measure-side rung quasi-isometric
to no finitely presented group at all, with the same construction on both sides and only
the dynamics changed. It would also give, through
`lef-infinite-simple-groups-are-qi-rigid`, an immediate second proof that the rung is not
LEF.

## Attempts

- **Steinberg cover.** `steinberg-finite-presentation-and-kazhdan-theorem`: for a
  finitely presented unital ring `R` and `n >= 4`, `St_n(R)` is finitely presented and
  surjects onto `EL_n(R)`. `L_k(1,d)` is finitely presented as a ring (generators
  `s_i, t_i`, relations `t_i s_j = δ_ij` and `Σ_i s_i t_i = 1`), so the cover is
  available. *Where it dies:* the kernel is `K_2(n, L_k(1,d))`, and finite presentation
  of `EL_n` needs that kernel to be finitely generated as a normal subgroup. The cited
  node explicitly declines to control it, and no centrality statement is available over a
  noncommutative ring.
- **Vanishing of `K_2`.** If `K_2(n, L_k(1,d)) = 0` then `St_n = EL_n` and the answer is
  yes. *Where it dies:* not computed here. The Eilenberg swindle that kills the stable
  `K`-theory of a properly infinite ring does not obviously descend to unstable
  `K_2(n, -)` at a fixed `n`.
- **Contrast with `cohn-elementary-group-is-not-lef`.** That node uses finite
  presentation of `St_4(J)` to refute LEF for the Cohn and Jacobson algebras, and it
  needs no control of `K_2`, because it only needs a homomorphism *out of* the cover.
  The present question needs finite presentation of the quotient, which is strictly more.
  So the existing machinery does not answer it.
- **Negative route.** A paradox-side rung could fail to be finitely presented for its own
  reasons, in which case the coarse separation stays as it is in
  `lef-infinite-simple-groups-are-qi-rigid`: measure side versus the non-MF paper's own
  finitely presented examples, rather than measure side versus paradox side inside the
  ladder. That would not damage anything already landed.
