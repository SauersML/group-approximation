---
rg: 2
id: pure-braid-sunflower-characters-obstruct-bnsr-invariants-proof
kind: route
title: Move the common puncture to infinity by the S_{n+1} symmetry and apply the product-projection obstruction
target: pure-braid-sunflower-characters-obstruct-bnsr-invariants
requires:
  - pure-braid-product-projections-obstruct-bnsr-invariants
artifacts:
  - research/artifacts/zp-pure-braid-bnsr-pencils-2026-09-13.md
---

Artifact `zp-pure-braid-bnsr-pencils-2026-09-13.md`, Sections 1–2.

1. Twist classes. In `H_1(H_n)`, a twist about a curve around a set `S` of
   punctures equals `sum_{pairs in S} T_{pair}`. This comes from the
   abelianization of `P_n`: all curves with the same labelled punctures inside
   are related by pure mapping classes. The twist around all punctures but one
   is trivial, so row sums vanish. For zero-sum `chi` on `P_n`, `c_{ij} = a_{ij}`
   for `i, j <= n`, and `c_{i,n+1} = -sum_j a_{ij}`.
2. Symmetry. `Mod(S_{0,n+1}) -> S_{n+1}` has kernel `H_n`. Conjugation acts on
   characters by permuting indices, and BNSR invariants are
   `Aut(H_n)`-invariant.
3. Choose `sigma` with `sigma(p) = n+1`. Then `sigma(U_i) = A_i ∪ {n+1}` with the
   `A_i <= [n]` pairwise disjoint and `|A_i| >= 3`. By item 1, `L_{A_i ∪ {n+1}}` is
   exactly the zero-sum characters supported inside `A_i`, and
   `sum(|A_i| - 2) = D`. So `pure-braid-product-projections-obstruct-bnsr-invariants`
   applies. Non-membership in `Sigma^D(P_n)` passes to `H_n` through the split
   projection `P_n -> H_n` (Meinert 1997, Corollary 2.8), and item 2 moves it
   back to the `U_i`.
