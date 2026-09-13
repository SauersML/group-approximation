---
rg: 2
id: two-piece-left-inverses-are-corner-left-inverses-proof
kind: route
title: Solve C (P + hP') = 1 separately on the two pieces
target: two-piece-left-inverses-are-corner-left-inverses
requires: []
artifacts:
  - research/artifacts/ternary-one-transvection-two-piece-lift-2026-09-12.md
---

## Why sufficient

Artifact Section 2. `a = u0 b` with `b = P + hP'`, so it suffices to treat `b`.

**Corner to whole ring.** For `v = P'vP'` with `v h P' = P'`, put `c' = P + v - P h v`.
- `c'P = P`, since `vP = 0`.
- `c' h P' = P h P' + P' - P h P' = P'`.
- So `c' b = 1`, and `c' u0^(-1)` is a left inverse of `a`.

**Whole ring to corner.** Put `C = c u0`, so `C b = 1`.
- Multiplying on the right by `P` gives `CP = P`; multiplying by `P'` gives `C h P' = P'`.
- Then `P'CP = 0`, so `P' = P'ChP' = (P'CP') hP'`.

Both directions are identities in an arbitrary unital ring. Nothing about the characteristic, the group or
the evaluation map is used.

*Verification by `w4-vf-linear-b` (2026-09-12), Section 41 of `research/artifacts/gk-vf-linear-b-verification-2026-09-12.md`: PASS. Both directions re-derived as identities in an arbitrary unital ring, together with Corollary A.1 and Construction C (`u0 s0 = s00`, `u1 s1 = s01`, `pi(a) = s0`). Not decision-level: `one-transvection-ternary-s0-lift-is-left-invertible` stays OPEN.*
