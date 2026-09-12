---
rg: 2
id: leavitt-rank-functions-two-root-defect-proof
kind: route
title: Quotient by the null ideal, extract matrix units, and use that the Leavitt algebra has no rank function
target: leavitt-rank-functions-killing-two-root-defect-are-augmentation
requires:
  - el3-unit-root-matrix-units-iff-two-root-identities
  - leavitt-gl-equals-el-and-perfect-unit-group
  - simple-group-rank-functions-are-augmentation-or-detecting
artifacts:
  - research/artifacts/sylvester-rank-function-two-root-gate-2026-09-12.md
---

Artifact Theorem 1. The easy direction: the augmentation kills both elements.

For the other direction:
1. **Quotient.** Pass to `B = K[Γ]/I_rk`, where `rk` is faithful on elements. The quotient map
   `σ : Γ -> B^x` satisfies both identities in `B`.
2. **Matrix units.** Theorem A of `el3-unit-root-matrix-units-iff-two-root-identities`, valid for any
   rings, gives matrix units `u_ij` on orthogonal idempotents `p_i`.
3. **Corner homomorphism.** The ring algebra of Propositions 6 and 8 and Corollary 9 in
   `research/artifacts/el3-rank-ring-rigidity-2026-09-12.md` is valid in any ring of characteristic `p`;
   this lane re-read its scope. It gives a unital ring homomorphism `R -> p_1 B p_1`.
4. **Collapse.** If `p_1 != 0`, `rk / rk(p_1)` is a Sylvester rank function on the corner. It pulls back
   to `R`, where `t_i s_i = 1` and `s_0 t_0 + s_1 t_1 = 1` force `1 >= 2`. So `p_1 = 0`, every root
   element dies, and `EL_3(R) = Γ` (`leavitt-gl-equals-el-and-perfect-unit-group`) dies.
5. **Conclusion.** Theorem 1.1(3) of `simple-group-rank-functions-are-augmentation-or-detecting` gives
   `rk = rk_ε`.
