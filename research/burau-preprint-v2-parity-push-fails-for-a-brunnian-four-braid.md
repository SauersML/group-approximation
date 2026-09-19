---
rg: 2
id: burau-preprint-v2-parity-push-fails-for-a-brunnian-four-braid
kind: claim
title: "Proposition 6.7 of arXiv:2607.05283v2 fails at every proper-product conjugate of the Brunnian braid Φ_0"
distinct_from:
  parity-correcting-push-fails-for-a-brunnian-four-braid: that claim compares crossing counts of parity-clean representatives and packages v1; this claim compares geometric intersection numbers as in the current version v2, checked verbatim against the v2 PDF, and applies the result to its Proposition 6.7 and Theorem 6.9
  brunnian-four-braids-admit-parity-correcting-push: that is the refuted universal packaging of v1 Proposition 6.4; this is the corresponding negative statement for v2 Proposition 6.7
artifacts:
  - research/artifacts/zp-burau-v2-audit-2026-09-19.md
  - experiments/burau-v2-audit-2026-09-17/section7_parity_calibration.py
  - experiments/burau-v2-audit-2026-09-17/section7_parity_calibration.log
---

Notation is that of arXiv:2607.05283v2 (V. Bharathram, J. S. Birman, T. E. Brendle, posted
2026-09-14).
- `α` is the arc from `p_1` to `p_2`, and `β_*^3` is the arc from the base point to `p_3`.
- `f : B_4 → B_5` is the standard inclusion, and `ι` is the geometric intersection number.
- "Parity condition" is the preprint's definition, p. 7, quoted in artifact §1.
- `Φ_0 = [(σ_1σ_2)^6, [A_14, [A_24, A_34]]]` is the nontrivial Brunnian braid of
  `burau-minus-one-kernel-meets-brunnian-four-braids`.

**Claim.** Let `Φ ∈ B_4` be any conjugate of any positive power of `Φ_0`, and let `Γ ∈ B_5` be
arbitrary. If `f(Φ)·Γ` and `Γ` both satisfy the parity condition, then
`ι(α, (β_*^3) f(Φ)Γ) = ι(α, (β_*^3) Γ)`.

**What it changes.** Proposition 6.7 of v2 asserts the opposite for every `Φ ∈ B_4` that is a
proper product `Φ′·Γ_1`: some `Γ ∈ K_5` makes both parity-clean, with unequal `ι`. Its
Corollary 6.8 and Theorem 6.9 need exactly that. So:
- **either** Proposition 6.7 is false at a proper-product conjugate of `Φ_0`,
- **or** `Φ_0` has no such conjugate, and the conjugation step in the proof of Theorem 6.9 is
  false.

Either way, the current version v2 of the only claimed proof does not prove that `ρ_4` is
faithful on `Brun_4`. "Minor corrections and improved exposition" did not repair the v1 gap.

The Moody-witness claim `brunnian-four-braids-have-five-strand-moody-witness` is untouched.

Route: `burau-preprint-v2-parity-push-fails-via-minimal-parity-arcs`.
