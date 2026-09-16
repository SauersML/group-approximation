---
rg: 2
id: parity-correcting-push-fails-for-a-brunnian-four-braid
kind: claim
title: "Some nontrivial Brunnian 4-braid has no conjugate power and five-strand push map giving parity-clean arcs with unequal counts"
distinct_from:
  brunnian-four-braids-admit-parity-correcting-push: that claim is the universal existence statement packaging Proposition 6.4 of arXiv:2607.05283; this claim is its negation, witnessed by one explicit braid
  brunnian-four-braids-have-five-strand-moody-witness: that claim asks only that some push map change the Moody polynomial; this claim says that for one braid no push map changes the parity-clean intersection counts, and leaves that claim open
artifacts:
  - research/artifacts/zp-burau-parity-t-minus-one-obstruction-2026-09-16.md
---

Notation is as in `brunnian-four-braids-admit-parity-correcting-push`:
- `α` is the arc from `p_1` to `p_2`, and `β_*^3` is the arc from the boundary base point to
  `p_3`;
- `f : B_4 → B_5` is the standard inclusion, and `K_5` is the point-pushing subgroup of `p_5`.

**Claim.** There is a nontrivial `Φ ∈ Brun_4` with the following property. For all `k ≥ 1`,
`y ∈ B_4` and `Γ ∈ K_5`, write `Φ_1 = y Φ^k y^{-1}`. Then any transverse representatives of
`A = (β_*^3) f(Φ_1) Γ` and `B = (β_*^3) Γ` that both satisfy the parity condition have
`|A ∩ α| = |B ∩ α|`.

The braid is `Φ_0 = [(σ_1σ_2)^6, [A_14, [A_24, A_34]]]` of
`burau-minus-one-kernel-meets-brunnian-four-braids`. The conclusion holds for every `Γ ∈ B_5`,
not only for `Γ ∈ K_5`.

This refutes `brunnian-four-braids-admit-parity-correcting-push`. Consequences:
- the route `five-strand-moody-witness-via-parity-correction` is invalidated;
- the mechanism of Section 6 of arXiv:2607.05283v1 cannot work for `Φ_0`, whatever step fails
  (artifact §10.1).

The witness claim `brunnian-four-braids-have-five-strand-moody-witness` stays open.

Route: `parity-correcting-push-fails-via-minus-one-kernel`.
