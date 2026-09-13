---
rg: 2
id: sylvester-rank-functions-are-submodular-on-stacked-rows
kind: claim
title: Sylvester matrix rank functions are submodular on stacked rows, so kernel containment after every right factor is transitive and closed under stacking
distinct_from:
  sylvester-rank-functions-descend-to-quotients-and-compressions: that builds new rank functions from ideal quotients and commuting compressions; this is an inequality for one rank function on stacks of three row blocks, and the containment calculus it gives.
artifacts:
  - research/artifacts/sylvester-exact-globality-and-kernel-compression-2026-09-12.md
---

**ESTABLISHED** (on paper, lane `w7-sylv-global`, route `sylvester-rank-functions-are-submodular-on-stacked-rows-proof`;
artifact Section 1; verified PASS by `w4-vf-linear-b`, Section 39.1 of
`research/artifacts/gk-vf-linear-b-verification-2026-09-12.md`, ae0a4005ef).

Let `rho` be a Sylvester matrix rank function on a unital ring `S`.

1. **Submodularity.** For matrices `A`, `B`, `C` over `S` with the same number of columns,
   `rho([A; B; C]) + rho(B) <= rho([A; B]) + rho([B; C])`.
2. **Containment calculus.** For columns `M`, `M'` over `S`, write `M ≼ M'` if `rho([M W; M' W]) = rho(M W)` for every
   matrix `W`, where `M W := (M (x) I) W`.
   - `M ≼ Y M` for every matrix `Y`.
   - `≼` is unchanged by invertible left factors and is preserved by right translation `M -> M v`.
   - By part 1 it is transitive and closed under stacking: `M ≼ M_1` and `M ≼ M_2` give `M ≼ [M_1; M_2]`.

In a regular rank ring, part 1 is the modular inequality `dim(a+b+c) + dim b <= dim(a+b) + dim(b+c)` for row modules,
and `M ≼ M'` is containment of kernels. Part 2 replaces principal right ideals in
`sylvester-leavitt-kazhdan-fixed-ideals-are-global`.

## Attempts

Established on paper, not open. Proof in artifact Section 1.
