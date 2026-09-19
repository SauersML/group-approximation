---
rg: 2
id: fpbs-free-product-meet-limit-equals-exp-decay-threshold-proof
kind: route
title: Factor the free-product two-point function across bridges, decay each coset factor by sharpness on the amenable factor, and close with the exponential sandwich
target: fpbs-free-product-meet-limit-equals-exp-decay-threshold
requires:
  - fpbs-replica-meet-cap-inf-fails-free-products
  - fpbs-hp-relative-sharpness
  - fpbs-replica-meet-limit-sandwiched-by-exp-decay-threshold
  - fpbs-kesten-square-lattice-pc-one-half
artifacts:
  - research/artifacts/fpbs/docs/replica-meet-exp-decay-threshold-2026-09-19.md
---

The complete proof is in Section 3 of the artifact.

1. **Factorisation (item 1).** Every `t`-edge is a bridge of `G`
   (`fpbs-replica-meet-cap-inf-fails-free-products`, item 2).
   - The `o`–`x` route in the coset tree crosses `m` bridges and passes
     through the planes `P_i = a_0 t ... a_{i-1} t A`, each a copy of `L`.
   - A path that leaves `P_i` through a bridge must return through the same
     bridge. So excursions can be cut out, and the entry and exit vertices of
     `P_i` are joined inside `P_i`. Those two vertices differ by right
     multiplication by `a_i`.
   - The bridge events and the plane events use disjoint edge sets, so the
     factorisation is exact.
   - The word length is additive over the free factors.
2. **Lower bound.** Apply `fpbs-hp-relative-sharpness` to `L` with `H = A`,
   which gives `p_c(A;L) = p_c(L)`.
   - For `p < p_c(L)`: `P_p(|K_e^L| >= n) <= e^{-cn}`, so
     `tau^L_p(e,a) <= e^{-c|a|}`.
   - With `eta = min(c, -log p)`, item 1 gives
     `tau^G_p(o,x) <= e^{-eta |x|_S}`.
   - So `xi_p > 0` and `p_exp(G) >= p_c(L)`.
3. **Upper bound.** Item 3 of `fpbs-replica-meet-cap-inf-fails-free-products`
   gives `p_cap^(k) <= p_c(L)` for every `k`.
4. **Chain.** Item 2 of
   `fpbs-replica-meet-limit-sandwiched-by-exp-decay-threshold` gives
   `p_exp <= sup_k p_k <= p_cap^(infty)`, so every inequality is an equality.
5. **Instance (item 3).** `p_c(Z^2) = 1/2` by
   `fpbs-kesten-square-lattice-pc-one-half`.
