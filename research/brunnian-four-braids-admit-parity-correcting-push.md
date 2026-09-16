---
rg: 2
id: brunnian-four-braids-admit-parity-correcting-push
kind: claim
title: Every nontrivial Brunnian 4-braid has a conjugate and a 5-strand push map giving parity-clean arcs with unequal intersection counts
distinct_from:
  brunnian-four-braids-have-five-strand-moody-witness: that claim is the existence of a five-strand push map changing the Moody polynomial; this claim is the stronger combinatorial statement Proposition 6.4 of arXiv:2607.05283 asserts (parity condition for both arcs plus unequal intersection counts), which implies that one
refuted_by:
  - parity-correcting-push-fails-for-a-brunnian-four-braid
artifacts:
  - research/artifacts/zp-burau-n4-verification-2026-09-13-part1.md
  - research/artifacts/zp-burau-n4-verification-2026-09-13-part2.md
---

Let `alpha` be the arc from `p1` to `p2`, `beta_*^3` the standard arc from the
boundary basepoint to `p3`, `f: B_4 -> B_5` the standard inclusion, and `K_5` the
point-pushing subgroup of `p5` in `B_5`. For every nontrivial `Phi` in the Brunnian
subgroup `Brun_4` there are `k >= 1`, `y` in `B_4` and `Gamma` in `K_5` with the
following property. Write `Phi_1 = y Phi^k y^{-1}`, `A = (beta_*^3) f(Phi_1) Gamma` and
`B = (beta_*^3) Gamma`. Then some transverse representatives of `A` and `B` both
satisfy the **parity condition**: a disk in the disk sequence is sign-changing iff it
contains an odd number of marked points. Moreover, `|A ∩ alpha| != |B ∩ alpha|` for
those representatives.

This packages Proposition 6.4 and the conjugation step of Theorem 6.6 of
arXiv:2607.05283v1 (Bharathram–Birman–Brendle), which state the case `k = 1`.
Allowing powers means a proof may assume `iota(alpha, (beta_*^3)Phi_1) > 0`, by
`brunnian-four-braid-powers-cross-the-base-arc` (lane z3-05-burau-theory). That
repairs gap G6.

- Route `five-strand-moody-witness-via-parity-correction`: this claim implies
  `brunnian-four-braids-have-five-strand-moody-witness`.
- Through the chain of lane z3-05-burau-theory
  (`brunnian-four-braids-avoid-burau-kernel-via-moody`, then
  `four-strand-burau-faithful-via-brunnian-braids`), it gives faithfulness of Burau
  on `B_4`.

## Attempts

- **The preprint's route.** arXiv:2607.05283v1, Section 6: conjugate `Phi` into a
  proper product `Phi'.Gamma_1`, list the possible disk types (Lemma 6.3), then build
  `Gamma = gamma_2 ∘ gamma_1` to turn 4-disks into 5-disks.
- **Check (z3-05-burau-search, 2026-09-13): not verified.**
  - Proposition 6.4's final step replaces `gamma_2` by `gamma' ∪ gamma'' ∪ gamma_2`
    and asserts two things without proof: that the intersection count strictly
    increases, and that the new loop still satisfies parity.
  - Lemmas 6.2–6.3 are supported by figures only.
  - The normalization "a freely reduced product is a proper product" is not proved.
  - Details, gaps G1–G6:
    `research/artifacts/zp-burau-n4-verification-2026-09-13-part2.md`.
- **Where it stands.** For a braid in the kernel, the two unproved facts in G1
  contradict each other. So this claim is no easier than the theorem for that braid,
  and a proof must choose `gamma''` with control over the new disk types.
- **2026-09-16 (swarm frontier lane hi-fron-zaremsky-3-05-four-strand-bura): false.**
  - Parity-clean arcs see only `M(alpha, .)(-1)`. So if `rho_n(Psi) = I mod (t+1)`,
    parity-clean representatives before and after `Psi` cross `alpha` equally often
    (`parity-clean-arc-counts-see-only-burau-mod-t-plus-one`).
  - The nontrivial Brunnian braid `Phi_0 = [(s1 s2)^6, [A14, [A24, A34]]]` has
    `rho_4(Phi_0) = I mod (t+1)` (`burau-minus-one-kernel-meets-brunnian-four-braids`).
  - So the claim fails for `Phi_0`, for all `k`, `y` and `Gamma`
    (`parity-correcting-push-fails-for-a-brunnian-four-braid`).
  - Artifact: `research/artifacts/zp-burau-parity-t-minus-one-obstruction-2026-09-16.md`.
