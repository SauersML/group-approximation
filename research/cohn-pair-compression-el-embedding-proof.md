---
rg: 2
id: cohn-pair-compression-el-embedding-proof
kind: route
title: Blockwise conjugation by a Cohn pair is multiplicative and absorbs the defect idempotent, and same-block generators are commutators of cross-block ones
target: cohn-pair-compression-embeds-el-2n-into-el-n
requires:
  - cohn-elementary-group-rank-radical-is-trivial-or-everything
  - thompson-v-lifts-into-rank-four-cohn-elementary-group
artifacts:
  - research/artifacts/cohn-elementary-group-compressions-and-lef-2026-09-12.md
---

The proof is in artifact Section 1 (Lemmas 1.1–1.2, Theorem 1.3, Remark 1.5) and Section 2
(Corollaries 2.1–2.4).

1. **The defect idempotent is absorbed.** `t_j q = 0 = q s_i` and `q^2 = q`, since `t_i s_j = delta_ij`.
2. **`iota` is multiplicative and injective.** Multiplicativity comes from `t_b s_c = delta_bc`, and
   injectivity from `t_c iota(x) s_d = x_cd`. Also `iota(x) q = q iota(x) = 0`, so `psi_n` is a
   homomorphism, and `psi_n(1) = (1-q) + q = 1`.
3. **Cross-block generators.** A generator between blocks `i != j` has identity diagonal blocks, so
   its image is `x_ij(s_a c t_b)`.
4. **Same-block generators.** For `n >= 2` and `j != i`,
   `x_((i,a),(i,b))(c) = [x_((i,a),(j,0))(c), x_((j,0),(i,b))(1)]`. So the elementary image lies in
   `EL_n`.
5. **Binary Cohn algebra.**
   - Iterating `psi` and using upper-left inclusions gives `EL_m(C_2) -> EL_n(C_2)`.
   - The unital embedding `J -> C_2` comes from
     `cohn-elementary-group-rank-radical-is-trivial-or-everything` (Lemma 2.1 of its artifact).
   - `pi o psi = psi^R o pi`, and `psi^R` is the Leavitt isomorphism, so the finitary kernels and
     their complements are preserved.
6. **V.** `psi_3` applied to `phi(V) (+) 1_4 <= EL_6(C_2)` gives `V' <= EL_3(C_2)`. It meets `K`
   trivially by step 5, because `pi o phi` is injective.

*Verified independently by `w4-vf-gate` (2026-09-12), Section 24.1 of `research/artifacts/gk-vf-gate-verification-2026-09-12.md`. PASS.*
