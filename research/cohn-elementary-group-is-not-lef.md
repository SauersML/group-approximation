---
rg: 2
id: cohn-elementary-group-is-not-lef
kind: claim
title: EL_3 over the binary Cohn algebra is not LEF, since it contains EL_4 of the Jacobson algebra, whose finitely presented Steinberg cover kills the head root in every finite image
distinct_from:
  binary-jacobson-elementary-mark-is-finite-quotient-invisible: that shows every finite image of EL_5(J) kills x_13(Q); this adds the finitely presented Steinberg cover to get non-LEF for every EL_n(J), n >= 4, and transfers it to EL_3(C_2) through the Cohn compression.
  leavitt-first-offdiagonal-core-is-marked-non-lef: that proves non-LEF for the one-branch Toeplitz core inside EL_5(R); this proves it for EL_n(J), n >= 4, and for every EL_m(C_2), m >= 2.
artifacts:
  - research/artifacts/cohn-elementary-group-compressions-and-lef-2026-09-12.md
---

**ESTABLISHED** (proof route `cohn-elementary-group-not-lef-proof`; artifact Section 3; independent
re-derivation requested from `w4-vf-gate`). It imports
`steinberg-finite-presentation-and-kazhdan-theorem` at statement level.

Let `J = F_2<S,T | TS=1>`, `Q = 1 - ST`, `C_2` the binary Cohn algebra.

1. **Finite images kill the head root.** In any group satisfying the Steinberg relations over `J` in
   indices 1, 2, 3, every finite image kills `x_13(Q)`.
   - By pigeonhole two of the `x_13(e_a0)` coincide, so `x_13(e_a0 + e_a'0)` dies.
   - The Steinberg commutators `x_13(r) -> x_12(r) -> x_32(Q) -> x_12(Q) -> x_13(Q)` then kill
     `x_13(Q)`.
2. **The finitely presented cover.** `St_4(J)` is finitely presented. If `EL_4(J)` were LEF, a finite
   partial embedding of the ball containing the relator prefixes would define a homomorphism
   `St_4(J) -> F` to a finite group that does not kill `x_13(Q)`.
3. **Transfer to C_2.** So `EL_n(J)` is not LEF for `n >= 4`. By
   `cohn-pair-compression-embeds-el-2n-into-el-n`, `EL_4(J) <= EL_m(C_2)` for every `m >= 2`, so no
   `EL_m(C_2)` is LEF.

**Consequences.**
- **LEF can't refute the identity.** Local embeddability cannot prove `EL_3(C_2)` sofic or linear
  sofic, so `cohn-coefficient-el3-rank-models-satisfy-two-root-identity` cannot be refuted through LEF.
- **Still open:** soficity and linear soficity of `EL_3(C_2)`.
- **Link to V:** the group contains `V`, so a sofic approximation of it would make `V` sofic.
