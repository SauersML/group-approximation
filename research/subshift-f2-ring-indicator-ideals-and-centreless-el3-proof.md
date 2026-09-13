---
rg: 2
id: subshift-f2-ring-indicator-ideals-and-centreless-el3-proof
kind: route
title: Proof by covering X with translates of the indicator and by separating a point from its translate
target: subshift-f2-ring-indicator-ideals-and-centreless-el3
requires: []
---
Notation as in the claim. Since `u e_V u^{-1} = e_{TV}`, we have `u^j e_V = e_{T^jV} u^j`.

**(1) Indicator ideals.**
- Let `I` be a two-sided ideal with `e_W ∈ I` and `W ≠ ∅` clopen. Then `e_{T^nW} = u^n e_W u^{-n} ∈ I` for every `n`.
- Every orbit is dense, so every `x` has some `T^n x ∈ W`, that is `x ∈ T^{-n}W`. So the translates of `W` cover `X`.
- By compactness, `X = T^{n_1}W ∪ … ∪ T^{n_k}W`.
- Expanding the product `∏_i (1 − e_{T^{n_i}W})` shows that `1 − ∏_i (1 − e_{T^{n_i}W})` is a sum of products, each containing some `e_{T^{n_i}W}`, so it lies in `I`.
- The product is the indicator of `X ∖ ⋃_i T^{n_i}W = ∅`, so it is `0`, and the element equals `1`. So `I = R`.

**(2) The centre of `G = EL_3(R)`.**
- Let `g ∈ Z(G)`.
  - For all `i ≠ j`, `g` commutes with `e_ij(1) = I_3 + E_ij`, so `g E_ij = E_ij g`. Comparing entries, `g = c I_3` with `c ∈ R`.
  - `c` is invertible because `g` is.
  - `g` commutes with `e_ij(e_V)` for every clopen `V`, so `c e_V = e_V c`.
- Write `c = Σ_j f_j u^j`. Then `e_V c − c e_V = Σ_j f_j (e_V − e_{T^jV}) u^j`.
- Suppose `f_j(x) ≠ 0` for some `j ≠ 0` and some `x`.
  - `T` has no periodic points (a finite orbit would be a proper closed invariant set), so `T^{-j}x ≠ x`.
  - Choose clopen `V` with `x ∈ V` and `T^{-j}x ∉ V`.
  - The `u^j`-coefficient at `x` is `f_j(x)(1_V(x) − 1_V(T^{-j}x)) = f_j(x) ≠ 0`. This contradicts `c e_V = e_V c`.
- So `c = f_0 ∈ LC(X,F_2)`.
- If `c r = 1` with `r = Σ_j g_j u^j`, the `u^0`-coefficient gives `f_0 g_0 = 1`. So `f_0` vanishes nowhere, and `f_0 = 1` because its values lie in `F_2`.
- So `g = I_3`.

**Use in the note.** At the end of the simplicity proof, `e_12(e_W) ∈ N` gives `e_W ∈ I_N`, so `I_N = R` by (1). Then `N` contains every `e_ij(r)`, because permutation matrices move elementary positions, and so `N = G`. The step "some `e_ij(s)` does not commute with `g`" uses (2).
