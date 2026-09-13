---
rg: 2
id: five-strand-moody-witness-via-parity-correction
kind: route
title: "Parity-clean arcs with unequal intersection counts give a five-strand Moody witness (Corollary 6.5 of arXiv:2607.05283)"
target: brunnian-four-braids-have-five-strand-moody-witness
requires:
  - brunnian-four-braids-admit-parity-correcting-push
artifacts:
  - research/artifacts/zp-burau-n4-verification-2026-09-13-part1.md
---

Let `1 != Phi` be in `Brun_4`. Take `y`, `Gamma` in `K_5`, `Phi_1 = y Phi y^{-1}`,
`A = (beta_*^3) f(Phi_1) Gamma` and `B = (beta_*^3) Gamma`, with transverse
representatives as in `brunnian-four-braids-admit-parity-correcting-push`.

1. **Winding identity.** Let `q_1, ..., q_m` be the crossings of a transverse
   representative with `alpha`, in order along the arc. Consecutive Moody exponents
   satisfy `k_{i+1} - k_i = W_i`, where `W_i` is the signed number of marked points
   of the disk bounded by the arc piece between `q_i` and `q_{i+1}` and a piece of
   `alpha` (Bigelow 1999, Section 3; Lemma 3.1 of the preprint).
   - This uses only that the two pieces form a simple closed curve. That holds
     because the arc piece has no interior crossing with `alpha`, so minimal
     position is not needed.
2. **No cancellation.** If `k_i = k_j`, the signed sum `W_i + ... + W_{j-1}` is
   `0`, so it is even. So an even number of odd disks lies between `q_i` and
   `q_j`. Under the parity condition that gives `epsilon_i = epsilon_j`. Hence the
   sum of the absolute values of the coefficients of `M(alpha, A)` is `|A ∩ alpha|`,
   and likewise for `B`.
3. **Witness.** `M(alpha, .)` is the equivariant algebraic intersection number of
   lifts, so it depends only on the isotopy class of the arc. The claim gives
   `|A ∩ alpha| != |B ∩ alpha|`, so the two coefficient sums differ. Multiplying by
   a unit `+-t^k` preserves that sum. So
   `M_{f(Phi_1).Gamma} != M_Gamma`, even up to units, and `Phi_1` is a conjugate of
   `Phi` in `B_4`.

This route replaces an earlier faithfulness route of this lane (landed
5c5c59481a, retired; see the verification artifact, part 2). That route
repeated the chain of lane z3-05-burau-theory:
`brunnian-four-braids-avoid-burau-kernel-via-moody`, then
`four-strand-burau-faithful-via-brunnian-braids`.
