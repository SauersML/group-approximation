---
rg: 2
id: brunnian-four-braid-powers-cross-the-base-arc
kind: claim
title: "Every nontrivial Brunnian 4-braid has a power that moves the arc to p_3 across the arc from p_1 to p_2"
artifacts:
  - research/artifacts/zp-burau-four-strand-mechanism-2026-09-13.md
---

In `D_4`, let `α` be the arc from `p_1` to `p_2`, and `β_*^3` the arc from the boundary base point
`p_*` to `p_3`. For every `1 ≠ Φ ∈ Brun_4`, the geometric intersection number
`ι(α, (β_*^3)Φ^k)` tends to infinity as `k → ∞`. In particular it is positive for some `k ≥ 1`.

**Consequence.** To prove `ker ρ_4 ∩ Brun_4 = 1`, it is enough to prove that no nontrivial
`Φ ∈ Brun_4` with `ι(α, (β_*^3)Φ) > 0` lies in `ker ρ_4`. Given any `1 ≠ Φ`, pick `k` with
`ι(α, (β_*^3)Φ^k) > 0`. Then `Φ^k` is nontrivial (`B_4` is torsion-free) and Brunnian, so
`Φ^k ∉ ker ρ_4`, and hence `Φ ∉ ker ρ_4`. The same holds with conjugates of powers, since
`Brun_4` is normal.

This repairs gap G6 of the check of arXiv:2607.05283v1 (artifact
`zp-burau-n4-verification-2026-09-13-part2.md`). That step of Theorem 6.6 needs
`ι(α, (β_*^3)Φ) > 0` for the braid being treated, and the preprint gives no proof. Replacing `Φ`
by a power supplies it. Route: `brunnian-four-braid-powers-cross-the-base-arc-proof`.
