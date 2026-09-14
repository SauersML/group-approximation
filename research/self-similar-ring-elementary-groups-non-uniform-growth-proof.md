---
rg: 2
id: self-similar-ring-elementary-groups-non-uniform-growth-proof
kind: route
title: R ≅ M_2(R) makes EL_n(R) ≅ EL_(n·2^k)(R) for all k, so the small-ball generating sets exist at every scale
target: self-similar-ring-elementary-groups-non-uniform-growth
requires: [el-small-ball-generating-sets-from-grigorchuk-levels, ejz-elementary-groups-explicit-kazhdan-constant]
artifacts:
  - research/artifacts/sk-free-8-nonuniform-growth-2026-09-13-part2.md
---

Artifact part 2, §4 (Lemma 4, Theorem A).
1. **Scales.** `R ≅ M_(2^k)(R)` by induction. Applying the ring isomorphism entrywise gives `EL_n(R) ≅ EL_n(M_(2^k)(R))`, and Lemma 4 (`EL_n(M_N(S)) = EL_(nN)(S)`) makes this `EL_(X_k × [n])(R)`.
   - Lemma 4 proof: block elementary matrices are products of elementary matrices with entries in different blocks. Conversely, an in-block `e_(ij)(r)` equals `[e_(ik)(r), e_(kj)(1)]` for `k` in another block.
2. **Growth rate.** The preimages `U_k` of `T_k(Σ)` generate `EL_n(R)`, with `|B_(U_k)(ℓ)| ≤ exp(Cℓ^β)` for `ℓ ≤ r_k/3` and constants independent of `k`. Submultiplicativity gives `ω(EL_n(R),U_k) ≤ |B(r_k/3)|^(3/r_k) ≤ exp(C(r_k/3)^(β−1)) → 1`.
3. **Exponential growth.** `EL_n(R)` has (T) for finitely generated `R` and `n ≥ 3` (Ershov–Jaikin-Zapirain, `ejz-elementary-groups-explicit-kazhdan-constant`). An infinite Kazhdan group is non-amenable, groups of subexponential growth are amenable, so `EL_n(R)` has exponential growth.
