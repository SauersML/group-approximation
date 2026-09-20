---
rg: 2
id: folner-torus-truncation-dichotomy-proof
kind: route
title: Transpose the truncated degree map to see an exact right annihilator, then count disjoint translates of annihilators in Følner sets on both sides
target: folner-torus-truncations-have-exact-or-linearly-deficient-rank
requires: []
artifacts:
  - research/artifacts/folner-torus-truncation-rank-dichotomy-2026-09-20.md
  - research/artifacts/lef-torus-small-fibre-2026-09-18.md
---

Full proof in `research/artifacts/folner-torus-truncation-rank-dichotomy-2026-09-20.md`, Sections 1–3.
Lemmas A and B are from `research/artifacts/lef-torus-small-fibre-2026-09-18.md`, Section 3.

1. **The truncation is an LRSF instance** (Lemma 1.1).
   - Lemma A supplies `W, eta`, and Lemma B supplies `F, mu'`.
   - Output `j` reads `jF ∩ E`, and input `i` is controlled by `iW`.
2. **Its `H^1` map** (Lemma 1.2) is `xi -> res_E(xi D)` on `Z^(dJ(E))`.
3. **Transpose** (Proposition 2.1).
   - Pairing gives `<xi D, v> = <xi, v D^*>`, and `v D^*` is supported in `E F^-1 <= J(E)`.
   - So the transpose is `v -> v D^*` with no truncation, and the rank defect is the dimension of
     the exact annihilator in `E`.
4. **Translates** (Lemma 3.1). In a right-Følner set, a finite `Sigma` has
   `|E|/|Sigma Sigma^-1| - o(|E|)` disjoint left translates. Left translates of annihilators are
   annihilators.
5. **Loop** (Theorem 3.2).
   - Right-regular implies exact full rank, by 3.
   - Asymptotically full rank implies left-regular: left annihilators give kernel vectors of the
     truncated map, by 4.
   - Left-regular implies rank `d|E| - o(|E|)`, because injectivity survives restriction up to the
     boundary `J F \ E`.
   - That bound implies right-regular: right annihilators give kernel vectors of the transpose,
     by 3 and 4.
