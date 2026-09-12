---
rg: 2
id: leavitt-crossed-product-coefficient-ring-is-k-trivial
kind: claim
title: The coefficient ring L_0^(⊗(d-1)) ⊗ L is semihereditary, regular supercoherent, and has vanishing K-theory in every degree
distinct_from:
  ara-cortinas-leavitt-tensor-k-theory-vanishes: that imports K_*(L_2 ⊗ R) = 0 for regular supercoherent R, and regular supercoherence of L; this derives the same three properties for the ultramatricial dilation L_0^(⊗(d-1)) ⊗ L, the coefficient ring of the crossed product decomposition.
  leavitt-tensor-global-dimension-bound: that bounds global dimensions of B ⊗ L^(⊗d); this uses its d = 1 case to get semihereditarity of a directed union of matrix rings over L.
artifacts:
  - research/artifacts/leavitt-tensor-crossed-product-2026-09-12.md
---

**ESTABLISHED (derivation from main's imports).** Let `k` be a field,
`L = L_k(1,2)`, `d >= 1`, and `C = L_0^(⊗(d−1)) ⊗ L`. Then:

1. `C` is left and right semihereditary, so every finitely presented `C`-module
   has projective dimension at most `1`;
2. `C[t_1, ..., t_p]` is regular coherent for every `p >= 0`, so `C` is regular
   supercoherent;
3. `K_n(C) = 0` for every `n ∈ Z`.

`C` is the coefficient ring of `leavitt-tensor-powers-are-twisted-crossed-products`.
The crossed product `C ∗ Z^(d−1) = L^(⊗d)` is not coherent
(`leavitt-tensor-powers-are-not-left-coherent`), but `C` has all three
properties.

Route: `leavitt-crossed-product-coefficient-ring-proof`.
