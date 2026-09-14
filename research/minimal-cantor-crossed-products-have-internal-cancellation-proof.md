---
rg: 2
id: minimal-cantor-crossed-products-have-internal-cancellation-proof
kind: route
title: Bounded Birkhoff sums from an equivalence, Gottschalk–Hedlund, Kakutani–Rokhlin level matching, and the clopen classification of idempotents
target: minimal-cantor-crossed-products-have-internal-cancellation
requires: [cantor-crossed-product-idempotents-similar-to-clopen-ones]
artifacts:
  - research/artifacts/sk-algebraic-putnam-2026-09-13-part2.md
---

Notation: `R = LC(X,F)⋊_TZ`, `(fu^i)(f′u^j) = f(f′∘T^{−i})u^{i+j}`, orbit representation at a point `x` (dense orbit).

1. **Bounded sums.** Let `x′ ∈ e_WRe_{W′}` and `y′ ∈ e_{W′}Re_W` with `x′y′ = e_W`, `y′x′ = e_{W′}`, propagations `≤ w`.
   - `x′` maps `V_{W′} = span{δ_t : T^tx ∈ W′}` isomorphically onto `V_W`.
   - For an interval `J = [m,m′)`, it maps `V_{W′} ∩ span{δ_t : m+w ≤ t < m′−w}` injectively into `V_W ∩ span{δ_t : t ∈ J}`. So `#(W′-times in J) − 2w ≤ #(W-times in J)`, and symmetrically.
   - So `|Σ_{t∈J}f(T^tx)| ≤ 2w` for `f = 1_W − 1_{W′}` and every interval `J`.
2. **Coboundary.** The orbit of `x` is dense. By the Gottschalk–Hedlund theorem (W. H. Gottschalk and G. A. Hedlund, *Topological Dynamics*, 1955; statement as in arXiv:1101.3523, introduction), `f = g∘T − g` with `g` continuous. Along the orbit `g(T^tx) − g(x) ∈ Z`, so by continuity and density `g − g(x) ∈ C(X,Z)`.
3. **Level matching.** Choose a nonempty clopen `Z` with `g|_Z` constant, and a Kakutani–Rokhlin partition over `Z` whose levels refine `{W,W′}`. In a tower of height `h` over `z ∈ Z`, `Σ_{j<h}f(T^jz) = g(T^hz)−g(z) = 0`, so it has equally many `W`-levels and `W′`-levels, and equally many `(X∖W)`- and `(X∖W′)`-levels.
4. **Units.** Let `γ` permute levels inside each tower, mapping `W`-levels onto `W′`-levels and the rest onto the rest. Then `γ ∈ [[T]]`.
   - For `γ = T^k` on `U_k`, put `w_γ = Σ_ke_{γU_k}u^k`. It is a unit with inverse `Σ_ke_{U_k}u^{−k}`, and `w_γe_Vw_γ^{−1} = e_{γV}` (as in `subshift-el-transvection-conjugacy-full-group-equivalence-proof`).
   - So `e_{X∖W} = 1−e_W` is similar to `e_{X∖W′}`. Conversely `γW = W′` gives `e_W ~ e_{W′}`. This proves part 2.
5. **Cancellation.** By `cantor-crossed-product-idempotents-similar-to-clopen-ones`, `e = he_Wh^{−1}` and `f = h′e_{W′}h′^{−1}`. If `eR ≅ fR` then `e_WR ≅ e_{W′}R`, so by steps 1–4 `(1−e_W)R ≅ (1−e_{W′})R`, so `(1−e)R ≅ (1−f)R`.
   - With `eR ≅ fR` this gives similarity: `v = x′′ + s′′` for the two equivalences `x′′ ∈ fRe` and `s′′ ∈ (1−f)R(1−e)` is a unit with `vev^{−1} = f`. ∎

**Model test.** The argument needs a dense orbit (step 2) and long towers (step 3). Both come from minimality.
