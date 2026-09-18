---
rg: 2
id: moody-witness-exists-iff-outside-burau-kernel
kind: claim
title: "A 4-braid has a five-strand Moody witness exactly when it lies outside the Burau kernel, with no power and no Brunnian hypothesis needed"
distinct_from:
  brunnian-four-braids-have-five-strand-moody-witness: that claim asserts that every nontrivial Brunnian 4-braid has a witness; this claim says that having a witness is the same as being outside ker rho_4, for every 4-braid, and makes no claim about which braids are outside
  moody-polynomial-change-certifies-burau-nonkernel: that claim is one direction (a witness certifies non-membership); this claim adds the converse for four-strand braids viewed in B_5 with push maps in K_5
  brunnian-four-braids-avoid-burau-kernel: that claim is the kernel statement for Brunnian braids; this claim is a braid-by-braid equivalence that turns it into the witness claim and back
artifacts:
  - experiments/moody-witness-equivalence-2026-09-17/spanning.py
  - experiments/moody-witness-equivalence-2026-09-17/spanning.log
  - research/artifacts/zp-burau-parity-t-minus-one-obstruction-2026-09-16.md
---

Use the notation of `brunnian-four-braids-have-five-strand-moody-witness` and the standard picture of
`research/artifacts/zp-burau-parity-t-minus-one-obstruction-2026-09-16.md` §1 and §10.3, with `n = 5`:
- the punctures `p_1, ..., p_5` lie on a horizontal diameter, and `p_*` is on the boundary below them;
- `α = [p_1, p_2]`, and `β_*^3` is the straight tail from `p_*` to `p_3`;
- `𝕄_Γ = 𝕄(α, (β_*^3)Γ)`;
- `f : B_4 → B_5` adds `p_5`, and `K_5 = π_1(D_4, p_5) ⊂ B_5`.

**Claim.** For every `Φ ∈ B_4` the following are equivalent:
1. `ρ_4(Φ) ≠ I`;
2. there are `y ∈ B_4` and `Γ ∈ K_5` with `𝕄_{f(yΦy^{-1})·Γ} ≠ 𝕄_Γ` (power `k = 1`);
3. there are `k ≥ 1`, a conjugate `Φ_0` of `Φ^k` in `B_4`, and `Γ ∈ K_5` with
   `𝕄_{f(Φ_0)·Γ} ≠ 𝕄_Γ`.

The composition convention for `f(Φ_0)·Γ` does not matter: the equivalence holds in both.

**Corollary.** `brunnian-four-braids-have-five-strand-moody-witness` is equivalent to
`brunnian-four-braids-avoid-burau-kernel`. Through the established Brunnian reduction
(`burau-four-faithful-iff-faithful-on-brunnian-braids`), it is equivalent to faithfulness of the
4-strand Burau representation. The witness hole is therefore not a strictly smaller step than the
flagship. It carries the whole problem, and the decomposition
`brunnian-four-braids-avoid-burau-kernel-via-moody` is a restatement, not a reduction.
