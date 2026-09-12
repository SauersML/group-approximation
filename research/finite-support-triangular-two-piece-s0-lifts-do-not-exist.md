---
rg: 2
id: finite-support-triangular-two-piece-s0-lifts-do-not-exist
kind: claim
title: No two-piece lift of s0 whose idempotent is supported on a finite subgroup has a vanishing off-diagonal defect
distinct_from:
  two-piece-s0-lift-with-triangular-defect-exists: that asserts some triangular two-piece lift exists, with no support condition; this refutes it for every idempotent supported on a finite subgroup and every h, leaving only idempotents whose support generates an infinite subgroup
artifacts:
  - research/artifacts/triangular-lift-hnn-transfer-2026-09-12.md
---

**ESTABLISHED** by route `finite-support-triangular-two-piece-lifts-refutation-proof`. Re-derivation requested from
`w4-vf-linear-b`.

Let `A = F_2[R^x]` with `R = L_(F_2)(1,2)` and evaluation `pi`. Take the data of
`two-piece-s0-lifts-telescope-to-a-corner`: an idempotent `E^` with `pi(E^) = s0t0`, units `g1, g2`, and
`h = g1^(-1)g2`. If `E^` is supported on a finite subgroup of `R^x`, then

    E^ [h] (1 - E^) != 0     and     (1 - E^) [h^(-1)] E^ != 0.

So the triangular shortcut never produces a witness for `left-invertible-lift-of-s0-in-leavitt-group-algebra` from a
finite-subgroup idempotent, whatever the units.

**Consequences.**
- **Dead candidates:**
  - the swap-group lifts, recovering the four-case Proposition 3.6 of
    `research/artifacts/binary-visible-lift-two-piece-telescoping-2026-09-12.md`;
  - the depth-`k` constants `GL_(2^k)(F_2)`, including `GL_4(F_2)`;
  - dyadic permutation constants, Klein constants and odd cyclic constants.
- **General supports.** A triangular witness with `K = <supp E^>` makes the group algebra of the HNN extension of `K`
  along conjugation by `h` not directly finite.
- **Survivors:**
  - idempotents whose support generates an infinite subgroup with that property;
  - finite-subgroup idempotents conjugated by units of `A`;
  - non-triangular unit products;
  - lifts with three or more pieces.
