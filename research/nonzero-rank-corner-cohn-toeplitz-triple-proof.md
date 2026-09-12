---
rg: 2
id: nonzero-rank-corner-cohn-toeplitz-triple-proof
kind: route
title: Pad the corner pair by the complementary idempotent and use rk(1 - ab) = rk(1 - ba)
target: nonzero-rank-corner-cannot-hold-a-cohn-toeplitz-triple
requires: []
artifacts:
  - research/artifacts/rank-four-corner-endpoint-and-framing-2026-09-12.md
---

This is Section 1, Theorem 1 of the artifact.

1. **The rank identity.** For square matrices `rank(1 - AB) = rank(1 - BA)`, because `v -> Bv` maps
   `ker(1 - AB)` bijectively onto `ker(1 - BA)`. The identity holds at every level of the ultraproduct,
   so `rk(1 - ab) = rk(1 - ba)` in `M` (Arzhantseva--Paunescu, Proposition 2.8).
2. **Padding.** Let `a = S_0 + (1 - e)` and `b = T_0 + (1 - e)`. Every cross term vanishes because
   `S_0` and `T_0` are in `eMe`, so `ba = T_0 S_0 + (1 - e) = 1` and `ab = S_0 T_0 + (1 - e)`.
3. **Conclusion.** `rk(e - S_0 T_0) = rk(1 - ba) = 0`. Faithfulness of `rk` on `M` gives `S_0 T_0 = e`.
4. **Consequences.**
   - For `S` in `eM` with `T_0 S = 0`: `S = eS = S_0 T_0 S = 0`.
   - With `S = S_1` and `T_1 S_1 = e`: `e = 0`.

*Verified independently by `w4-vf-gate` (2026-09-12), Section 2.1 of `research/artifacts/gk-vf-gate-verification-2026-09-12.md`. PASS.*
