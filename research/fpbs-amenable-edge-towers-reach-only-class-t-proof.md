---
rg: 2
id: fpbs-amenable-edge-towers-reach-only-class-t-proof
kind: route
title: Retract each graph of groups onto its vertex group modulo incident edge groups, and descend the tower
target: fpbs-amenable-edge-towers-reach-only-class-t
requires: []
---

Full details are in §1 of
`research/artifacts/fpbs-amenable-edge-tower-reach-2026-09-17.md`.

1. **`T` is closed under quotients** (induction on `r`). If `pi: Q ->> P` and
   `Q/<<M>> in T_{r-1}`, then `P/<<pi(M)>>` is a quotient of `Q/<<M>>`, and
   `pi(M)` is amenable.
2. **Finitely generated groups lie in `T`.** Kill the generators' cyclic
   subgroups one at a time. The same argument shows `AG ⊆ T`.
3. **Retraction.** Let `G` be the fundamental group of a finite graph of
   groups with amenable edge groups, and let `Gamma` be a vertex group. Let
   `N` be the normal closure in `Gamma` of the finitely many incident
   edge-group images `C_1, ..., C_p`. Define a map on Serre's presentation:
   send `Gamma` to `Gamma/N`, and send every other vertex group and every edge
   letter to `1`. It respects every relation, since every edge-group element
   in `Gamma` is killed, so `Gamma/N` is a quotient of `G`.
4. **Descent.** `K_n in T`. If `K_j in T`, then `K_{j-1}/N_j in T` by 1 and 3.
   Killing `C_1`, then the image of `C_2`, and so on gives `K_{j-1} in T`.
5. **Infinite free products.** Let `Q = *_{i in I} G_i` with `I` infinite.
   Every quotient reached by `r` steps has the form
   `P * *_{i ∉ S} G_i` with `S` finite.
   - By the Kurosh subgroup theorem, an amenable subgroup of such a free
     product lies in a conjugate of a factor, or is `Z` or `Z/2 * Z/2`, which
     are finitely generated. Any other free product of nontrivial groups
     contains `F_2`.
   - So its normal closure is normally generated inside `P * *_{i in S'} G_i`
     for a finite `S'`.
   - `(P' * R)/<<X>> = (P'/<<X>>) * R` when `X ⊆ P'`.
   - The last quotient is therefore nontrivial. By 1, no group surjecting onto
     `Q` is in `T`. `∎`

References: Serre, *Trees*, I.4–I.5 (presentation of the fundamental group of
a graph of groups); Kurosh subgroup theorem (Serre, *Trees*, I.5.5).
