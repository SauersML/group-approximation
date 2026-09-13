---
rg: 2
id: brunnian-four-braids-avoid-burau-kernel
kind: claim
title: "No nontrivial Brunnian 4-braid lies in the kernel of the 4-strand Burau representation"
distinct_from:
  four-strand-burau-representation-is-faithful: that claim is injectivity of Burau on all of B_4; this claim is injectivity on the free normal subgroup Brun_4, which is equivalent to it only through Long's theorem
---

For every `1 ≠ Φ ∈ Brun_4`, `ρ_4(Φ) ≠ I`. This is Theorem 6.6 of arXiv:2607.05283v1
(Bharathram–Birman–Brendle, unrefereed).

## Attempts

- 2026-09-13 (lane z3-05-burau-theory): the preprint's chain for this theorem is:
  - B1: nontrivial Brunnian 4-braids are pseudo-Anosov. Independently proved:
    `brunnian-four-braids-are-pseudo-anosov`.
  - B2: conjugate `Φ` to a proper product `Φ'·Γ_1` with `ι(α, (β_*^3)Φ) > 0` (Lemma 6.3).
    NOT checked here.
  - B3: for the inclusion `f : B_4 → B_5`, some push map `Γ ∈ K_5 = π_1(D_4, p_5)` makes
    `f(Φ)·Γ` a proper product; `f(Φ)·Γ` and `Γ` both satisfy the parity condition; and their
    intersection numbers with `α` differ (Proposition 6.4, Corollary 6.5). NOT checked here. It
    is recorded as `brunnian-four-braids-have-five-strand-moody-witness`.
  - B4: parity condition means no cancellation in the Moody polynomial (Lemma 4.2), and proper
    products are in minimal position (Proposition 5.1). The logic of Lemma 4.2 agrees (artifact
    §2.7); Proposition 5.1 is NOT checked.
  - B5: Moody's criterion (Theorem 2.3): recorded as
    `moody-polynomial-change-certifies-burau-nonkernel`.
  - B6: `f(Φ) ∉ ker ρ_5 ⇒ Φ ∉ ker ρ_4`. Independently proved:
    `burau-kernel-restricts-along-strand-inclusion`.
- The route `brunnian-four-braids-avoid-burau-kernel-via-moody` assembles B1–B6. It stays open
  until the two open inputs are established by a line-by-line check (lane z3-05-burau-search,
  artifact `zp-burau-n4-verification-2026-09-13*`) and a verifier review.
