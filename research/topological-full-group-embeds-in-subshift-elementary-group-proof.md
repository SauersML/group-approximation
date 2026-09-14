---
rg: 2
id: topological-full-group-embeds-in-subshift-elementary-group-proof
kind: route
title: Full-group units, Whitehead matrices, the index by flux and Kakutani--Rokhlin level permutations put the topological full group in EL_3
target: topological-full-group-embeds-in-subshift-elementary-group
requires:
  - derived-full-group-of-cantor-minimal-system-is-simple
  - derived-full-group-fg-iff-minimal-subshift
  - minimal-cantor-full-groups-are-amenable
artifacts:
  - research/artifacts/sk-subgroups-full-group-inside-2026-09-13-part1.md
---

The complete proof is artifact part 1, §§1–2. The embeddings (A) and (B) are proved there directly; the three requires are
used only for the properties of `[[T]]'` in the Consequence.

1. **Lemma 1.** `w_g = Σ_n u^n e_{n_g=n}` satisfies:
   - `w_g w_h = w_{gh}`, from `u^n e_A u^m e_B = u^{n+m} e_{T^{-m}A ∩ B}`;
   - `w_g e_V = e_{gV} w_g`;
   - `w_g = 1` only for `g = 1`.
2. **Lemma 2 (Whitehead).** `e_12(a)e_21(a^(-1))e_12(a)e_12(1)e_21(1)e_12(1) = diag(a,a^(-1))` in characteristic 2. Also
   `diag(aba^(-1)b^(-1),1) = diag(a,a^(-1))diag(b,b^(-1))diag((ba)^(-1),ba)`.
3. **Corollary A.** By Lemmas 1 and 2, `g ↦ diag(w_g,1,1)` is an injective homomorphism `[[T]]' -> EL_3(R)`.
4. **Index by flux.** `I(g) = ind(ĝ^(-1)N, N)` on the orbit of a fixed point `y`. It is additive, `I(T) = 1`, and `I = 0`
   on elements of finite order.
5. **Lemma 3.** A level permutation of a tower `T^aW`, `0 <= a < h`, maps to the image of a permutation matrix under the
   homomorphism `GL_(3h)(F_2) -> G`. That homomorphism sends transvections to `e_pq(E_ab)` or to
   `[e_pq(E_ab), e_qp(E_bb)]` (note l.205–215), so its image lies in `G`.
6. **Lemma 4.** Every `g ∈ [[T]]` is `T^k σ̃^(-1) h`, where:
   - `k = I(g)`;
   - `σ̃` is a level permutation that corrects the flux near 0 on a tower over `V ∋ y` whose `4M+1` levels are disjoint;
   - `h` preserves the forward orbit of `y`, and therefore permutes the levels of a Kakutani–Rokhlin partition with base
     `Y ∋ y`, return times `> 2M'`, and `n_h` constant on levels. This is shown by three cases on the level index.
7. **Theorem B.** `diag(w_g, u^(-I(g)), 1)` is multiplicative slot by slot and injective. Its generators are Whitehead matrices
   (`T`) or lie in `G` by Lemma 3.
