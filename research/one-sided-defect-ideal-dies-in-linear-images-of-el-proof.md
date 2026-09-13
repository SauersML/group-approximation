---
rg: 2
id: one-sided-defect-ideal-dies-in-linear-images-of-el-proof
kind: route
title: Rank-four compression cell, rigid-target lemma, then Steinberg commutators spread e_13(e) to E_N(R,ReR)
target: one-sided-defect-ideal-dies-in-linear-images-of-el
requires: [compression-defects-die-in-rigid-targets]
artifacts:
  - research/artifacts/un-open-8-target-agnostic-compression-2026-09-13.md
  - non_mf_groups_exist.tex
---

1. **The cell.** The printed rank-four compression cell (tex Lemma l.866) holds for every unital ring with `ts = 1`.
   In `EL_4(R)`, with `L = EL_3(R)` on coordinates `1,2,3`, there are `u, c` with `uLu^-1 <= L`, `c in C(L)` and
   `[ucu^-1, e_23(1)] = e_13(e)`.
2. **Embedding.** Embed `EL_4(R)` in `EL_N(R)` on the first four coordinates. The relations persist, so
   `e_13(e) in D_(EL_N R)(L)`.
3. **Rigid targets.** By `compression-defects-die-in-rigid-targets`, `ψ(e_13(e)) = 1` for every finite or linear `ψ`.
4. **Steinberg spread.** Using `[e_ij(x), e_jk(y)] = e_ik(xy)` for distinct `i,j,k`:
   - `[e_13(e), e_32(b)] = e_12(eb)`;
   - `[e_31(a), e_12(eb)] = e_32(aeb)`.

   So `e_32(aeb) in ker ψ`.
5. **All roots.** Conjugation by `w_ij = e_ij(1)e_ji(-1)e_ij(1)` moves this root to every `e_ij(±aeb)`. By additivity,
   `e_ij(x) in ker ψ` for all `x in ReR`.
6. **Conclusion.** `E_N(R, ReR)` is by definition the normal closure in `EL_N(R)` of these generators.
7. **Simple case.** If `R` is simple and `e != 0`, then `ReR = R`.

Details: artifact §3.
