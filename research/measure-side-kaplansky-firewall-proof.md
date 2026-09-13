---
rg: 2
id: measure-side-kaplansky-firewall-proof
kind: route
title: Elek's measure-preserving free minimal actions contain the group algebra as a unital subring
target: measure-side-stable-finiteness-contains-char-p-kaplansky
requires:
  - elek-free-minimal-cantor-actions-with-invariant-measures
artifacts:
  - research/artifacts/un-paradox-groupoid-tarski-2026-09-13-part2.md
---

## Why sufficient

1. **Finite groups.** `k[Γ]` is finite dimensional, hence stably finite.
2. **Countably infinite groups.** `elek-free-minimal-cantor-actions-with-invariant-measures` gives a free
   minimal Cantor action with an invariant probability measure.
   - The map `sum c_g g ↦ sum c_g 1_X u_g` is a unital ring homomorphism `k[Γ] -> LC(X,k) ⋊ Γ`. It is
     injective, because the crossed product is a free left `LC(X,k)`-module on the `u_g`.
   - A one-sided inverse in `M_m(k[Γ])` is one in `M_m(LC(X,k) ⋊ Γ)`, which is directly finite by
     hypothesis. So `M_m(k[Γ])` is directly finite.
3. **Arbitrary groups.** An equation `TS = 1` in `M_m(k[Γ])` involves finitely many group elements. They
   generate a countable subgroup `H`, and `k[H] ⊆ k[Γ]` is a unital subring.
