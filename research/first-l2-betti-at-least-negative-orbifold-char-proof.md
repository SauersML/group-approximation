---
rg: 2
id: first-l2-betti-at-least-negative-orbifold-char-proof
kind: route
title: Replace each orbit of relator cells by one cell per coset of the root, which has the same boundary span and von Neumann dimension 1/o_G(r)
target: first-l2-betti-at-least-negative-orbifold-char
requires:
  - l2-betti-numbers-vanish-with-infinite-normal-amenable-subgroup
---

Let `Z` be the Cayley 2-complex, the universal cover of the presentation
complex of `<X | R>`. Its cells are `G` vertices, `G x X` edges and `G x R`
2-cells; the 2-cell `(g, r)` is attached along the path from `g` reading `r`.
The action is free and cocompact, and `Z` is simply connected, so
`b_1^(2)(G) = b_1^(2)(Z; G)`. In the cellular L2-chain complex
`l^2(G)^R -> l^2(G)^X -> l^2(G)`:

1. **`dim_G ker d_1 = |X| - 1`.** The adjoint `d_1^*` sends `f in l^2(G)` to
   the differences of `f` along edges. Its kernel consists of the constant
   functions, which are `0` in `l^2(G)` since `G` is infinite. So the image of
   `d_1` is dense, of dimension `1`, and additivity of von Neumann dimension
   gives `dim_G ker d_1 = |X| - 1`.

2. **The relator cells span the same boundaries as one cell per coset.** Fix
   `r = u^n` with `u = u_r` and `o = o_G(r)`. For `g in G`, let `c_g` be the
   1-chain of the path from `g` reading `u^o`. It is a cycle, since `u^o = 1`
   in `G`, and `c_(g u) = c_g`, because the path from `g u` reading `u^o` is
   the same closed path started one `u`-block later. So `c_g` depends only on
   the coset `g<u>`. The path from `g` reading `u^n` runs through that closed
   path `n/o` times, so `d_2(g, r) = (n/o) c_g`. Hence the image of `d_2` on
   finitely supported chains is the span of the `c_(g<u_r>)` over all
   `r in R` and cosets.

3. **Dimension of the boundary space.** Let `T_r: l^2(G/<u_r>) -> l^2(G)^X`
   be the bounded equivariant map sending the point mass at `g<u_r>` to
   `c_(g<u_r>)`. It is bounded because every `c` has at most `o |u_r|` edges,
   each meeting boundedly many cycles of a fixed shape. By step 2, `d_2` and
   `T = sum_r T_r` have the same image on finitely supported chains. Both are
   bounded with dense finitely supported chains in their domains, so the
   closures of their images coincide. Therefore

   ```text
   dim_G closure(im d_2) = dim_G closure(im T)
                         <= sum_r dim_G l^2(G/<u_r>) = sum_r 1/o_G(r),
   ```

   using `dim_G l^2(G/H) = 1/|H|` for a finite subgroup `H`, the trace of the
   projection `(1/|H|) sum_(h in H) h`.

4. **Conclusion.**
   `b_1^(2)(G) = dim_G ker d_1 - dim_G closure(im d_2) >= |X| - 1 - sum_r 1/o_G(r)`.

**Corollary.** An infinite amenable `G` is an infinite normal amenable
subgroup of itself. So `l2-betti-numbers-vanish-with-infinite-normal-amenable-subgroup`
gives `b_1^(2)(G) = 0`, hence `chi_G(X,R) >= 0`. ∎

On the boundedness in step 3: `T_r` is a finite sum of translation-type
operators along the finitely many edges of one closed path. Each has norm at
most `1` on `l^2(G/<u_r>)`, and the number of edges of the path is `o |u_r|`.
