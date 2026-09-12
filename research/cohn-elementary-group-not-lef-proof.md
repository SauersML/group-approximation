---
rg: 2
id: cohn-elementary-group-not-lef-proof
kind: route
title: Pigeonhole plus a Steinberg commutator chain kills the head root in finite images, and the finitely presented Steinberg cover turns that into non-LEF
target: cohn-elementary-group-is-not-lef
requires:
  - cohn-pair-compression-embeds-el-2n-into-el-n
  - cohn-elementary-group-rank-radical-is-trivial-or-everything
  - steinberg-finite-presentation-and-kazhdan-theorem
artifacts:
  - research/artifacts/cohn-elementary-group-compressions-and-lef-2026-09-12.md
---

The proof is in artifact Section 3, Theorem 3.1.

1. **Pigeonhole and the chain.** With `e_ab = S^a Q T^b`, two of the `x_13(e_a0)` agree in a finite
   image. Take `r = e_a0 + e_a'0`. Then:
   - `[x_13(r), x_32(1)] = x_12(r)`;
   - `[x_31(e_0a), x_12(r)] = x_32(Q)`;
   - `[x_13(1), x_32(Q)] = x_12(Q)`;
   - `[x_12(Q), x_23(1)] = x_13(Q)`.
2. **The finitely presented cover.** `St_4(J)` is finitely presented. A LEF partial embedding of the
   finite set of relator-prefix images, the images of the generators, and the prefixes of a word for
   `x_13(Q)` extends to a homomorphism to a finite group. By injectivity, that homomorphism keeps
   `x_13(Q) != 1`, contradicting step 1.
3. **Subgroups.** LEF passes to subgroups, and `EL_4(J) <= EL_m(C_2)` by the compression and the
   unital embedding `J -> C_2`.

*Verified independently by `w4-vf-gate` (2026-09-12), Section 24.3 (the finite presentation of St_4(J) is imported at statement level) of `research/artifacts/gk-vf-gate-verification-2026-09-12.md`. PASS.*
