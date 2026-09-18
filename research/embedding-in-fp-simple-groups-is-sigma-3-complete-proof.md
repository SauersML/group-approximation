---
rg: 2
id: embedding-in-fp-simple-groups-is-sigma-3-complete-proof
kind: route
title: COF reduces to embeddability in DV_F through the cofinite/noncomputable splitting and circulant graph wreath products
target: embedding-in-fp-simple-groups-is-sigma-3-complete
requires:
  - boone-higman-is-equality-of-two-sigma-3-index-sets
  - circulant-graph-wreath-products-satisfy-boone-higman
  - simple-envelope-forces-solvable-word-problem
  - one-fp-simple-group-contains-every-brin-thompson-subgroup
---

Lane proof, not reviewed.

- **Upper bounds.**
  - `EMB ∈ Σ_3`, by item 1 of `boone-higman-is-equality-of-two-sigma-3-index-sets`.
  - `EMB_{DV_F} ∈ Σ_3`: an embedding is words `φ(a), φ(t)` in the generators of
    `DV_F` such that
    - (hom) `∀r ∈ W_i`, `φ(r) = 1`, which is `Π_2`;
    - (injective) `∀w (w =_{G_i} 1 ∨ φ(w) ≠ 1)`. Here `φ(w) ≠ 1` is decidable,
      since `DV_F` is finitely presented and simple, so this is `Π_2`.
- **Hardness.** Use the splitting lemma of
  `boone-higman-is-equality-of-two-sigma-3-index-sets-proof`. It is computable
  `i ↦ U_i ⊆ N_{≥1}` with:
  - `W_i` cofinite ⇒ `U_i` cofinite;
  - `W_i` coinfinite ⇒ `U_i` noncomputable.

  Map `i` to the c.e. presentation of `G_{U_i}`, which is computable.
  - **Cofinite `W_i`.** `G_{U_i} ≤ DV_F` by
    `circulant-graph-wreath-products-embed-in-dv-f-proof`, so it lies in both
    sets.
  - **Coinfinite `W_i`.** `U_i ≤_T WP(G_{U_i})`, via the test words
    `[a, t^k a t^{-k}]`, so the word problem is undecidable. Kuznetsov
    (`simple-envelope-forces-solvable-word-problem`) then puts `G_{U_i}` outside
    `EMB ⊇ EMB_{DV_F}`.
- **Conclusion.** `COF ≤_m EMB_{DV_F}` and `COF ≤_m EMB` by the same map. `COF` is
  `Σ_3`-complete (Rogers; Soare IV.3.5). ∎

**Scope.**
- **Finite presentations.** The version for finite presentations (`EMB_fp`) is not
  covered. A finitely presented version of the family, uniform in `i`, whose
  cofinite members still embed in a finitely presented simple group, is not
  supplied. Clapham overgroups are not known to embed.
