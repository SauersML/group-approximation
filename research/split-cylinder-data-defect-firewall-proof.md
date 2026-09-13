---
rg: 2
id: split-cylinder-data-defect-firewall-proof
kind: route
title: Prefix-replacement swaps, a trivial wreath kernel, and permuted tensor powers of a rank model
target: split-cylinder-data-cannot-force-defect-submultiplicativity
requires: []
artifacts:
  - research/artifacts/multiletter-split-borel-and-coefficient-firewalls-2026-09-12.md
---
Artifact Section 2 (Lemmas 2.1 and 2.2, Proposition 2.3, Corollary 2.4). Held OPEN until `w4-vf-gate` re-derives it.
1. **Swaps** (Lemma 2.1). `tau S[A] = S[B]` and `T[A] tau = T[B]`, so conjugation by `tau` moves `iota_A` to `iota_B`.
2. **Wreath product** (Lemma 2.2). A kernel element centralizes `G^k`. A nontrivial permutation part moves some
   `iota_(A_i)(G)` to a different `iota_(A_j)(G)`, so the kernel is trivial.
3. **Tensor model** (Proposition 2.3).
   * `rk(X (x) Y - X' (x) Y') <= rk(X - X') + rk(Y - Y')`, so permuted tensor powers of stages are asymptotic
     homomorphisms.
   * Defects in distinct slots multiply.
   * The fixed space lies inside `ker(col_S)` tensored with the other slots.

*Verified independently by `w4-vf-gate` (2026-09-12), Section 35.1 of `research/artifacts/gk-vf-gate-verification-2026-09-12.md`. PASS.*
