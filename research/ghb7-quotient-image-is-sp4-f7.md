---
rg: 2
id: ghb7-quotient-image-is-sp4-f7
kind: claim
title: The CCKW quotient of GHB_2(7) has image Sp_4(F_7), so the congruence kernel has index 276595200 and b_2 = 159091199
distinct_from:
  cckw-ghb2-kms-group-structure: that imports the CCKW statements, including homomorphisms GHB_2(p) -> SL_(4k)(F_q); this computes the exact image of the k = 1, q = 7 homomorphism and finds a symplectic group, which the source does not state
  ghb7-congruence-kernel-hyperbolic-kazhdan-with-large-b2: that proves b_2(H) >= 1380 without computing the index; this computes the index and the exact Betti and L2-Betti numbers of H
---

**ESTABLISHED** by [[ghb7-quotient-image-sp4-proof]].

Let `ψ : G_{HB_2}(7) → GL_4(F_7)` be the homomorphism of
`GroupApproximation/Kazhdan/GHBQuotientMatrices.lean`:

```text
a ↦ I + E_03 + E_12,   b ↦ I + E_10 − E_23,   c ↦ I + E_31.
```

1. **Invariant form.** The image preserves the nondegenerate alternating form
   `B = [[0,0,6,0],[0,0,0,6],[1,0,0,0],[0,1,0,0]]`, unique up to scalar.
2. **Image.** `ψ(G_{HB_2}(7)) = Sp_4(F_7) = Sp(B)`, of order `276595200`. It is not
   `SL_4(F_7)`.
3. **Kernel invariants.** For `H = Ker ψ`:

   ```text
   [G:H]        = 276595200 = 2401 · 115200,
   χ(H)         = 115200 · 1381 = 159091200,
   b_2(H; Q)    = 159091199,
   b_2^(2)(H)   = 159091200.
   ```

   The last line uses `ghb7-l2-betti-two-is-orbifold-euler-characteristic`.

**Correction to earlier wording.** Nodes that say "the `SL_4(F_7)` quotient" are right
that `ψ` maps into `SL_4(F_7)`. Its image is the symplectic subgroup, not the whole
group.
