---
rg: 2
id: accumulating-minimal-sets-el-restriction-kernel-elementary
kind: claim
title: Restriction kernels of EL_n over a subshift crossed product are relative elementary even when minimal subsets accumulate on the subsystem
distinct_from:
  restriction-kernel-relative-elementary-off-minimal-sets: that is the separated case; this is the remaining case, where the minimal subsets outside Y accumulate on Y and neither a retraction nor a clopen invariant splitting exists
artifacts:
  - research/artifacts/sk-k2-recurrent-2026-09-13.md
---

**OPEN.** Let X ⊆ A^Z be a subshift without periodic points, Y ⊆ X closed invariant and n ≥ 3.

Claim: ker(EL_n(R_X) → EL_n(R_Y)) = E_n(R_X, I_Y); equivalently, K_2(n,R_X) → K_2(n,R_Y) is onto.

Known cases (all unreviewed):
- minimal subsets outside Y form a closed set disjoint from Y (`restriction-kernel-relative-elementary-off-minimal-sets`);
- Y is an equivariant retract (`equivariant-retract-splits-subshift-el-restriction`);
- X∖Y is a union of clopen invariant sets (`clopen-invariant-complement-el-kernel-is-elementary`).

## Attempts
- **Element-wise Z.**
  - For one g, take Z = W_{V,J}, the closed invariant set of points visiting V in every interval of length J. It is disjoint from Y.
  - The lifting step of Theorem D replaces g by g h^{-1}. Its coefficients carry the exponents of a factorization of g|_Z, so J grows and minimal subsets outside Z can enter. The argument does not close.
- **Stable range.** The stable K_2(R_Y) = 0 (`binary-cantor-ring-stable-steinberg-group-centrally-closed`). So each g in the kernel lies in E_m(R_X,I_Y) for some m ≥ n. Whether m = n works is the question.
- **No counterexample.** A counterexample needs a class in K_2(3,R_Y) outside the image of K_2(3,R_X). The only known nonzero unstable classes over F_2 come from K_2(3,F_2) = Z/2, and those lift through F_2 ⊆ R_X.
