---
rg: 2
id: free-minimal-crossed-products-are-simple-with-rank-models-proof
kind: route
title: Freeness isolates a clopen idempotent, minimality spreads it, and box truncations are exact off the boundary
target: free-minimal-crossed-products-are-simple-with-rank-models
requires: [halvable-corner-makes-elementary-groups-nonsofic]
artifacts:
  - research/artifacts/free-minimal-crossed-product-rings-and-permutive-rigidity-2026-09-13.md
---

The artifact, Sections 1 and 2, gives the complete proofs.

1. **Simple.** For `0 != P = sum f_g u^g` with `f_0(x) = c != 0`, choose a clopen `W ∋ x` on which
   `f_0 = c` and `W ∩ σ^(-g) W = ∅` for the finitely many `g != 0` in the support. This uses
   freeness. Then `chi_W P chi_W = c chi_W`. Finitely many translates of `W` cover `X` by
   minimality, and inclusion–exclusion gives `1`.
2. **Centres.** A central element has `f_g (chi_W - chi_(σ^(-g) W)) = 0` for every clopen `W`, so
   `f_g = 0` for `g != 0`. The invariant locally constant `f_0` is constant. Scalar matrices commuting
   with all roots have central entries.
3. **Følner models.** Let `R` act on `k`-valued functions on the orbit of `x` by
   `(u^g xi)(h) = xi(h+g)` and `(f xi)(h) = f(h.x) xi(h)`, and truncate to `F_n = [0,n)^d`.
   - The multiplicativity defect is `Pi rho(a) (1 - Pi) rho(b) Pi`. Its rank is at most the
     `w`-boundary of `F_n`, where `w` bounds the propagation of `b`.
   - For `r != 0`, step 1 gives `s r t = chi_W`.
   - `chi_W` has rank equal to the number of visits of `F_n . x` to `W`. That is at least
     `n^d / |K| - o(n^d)`, where `K` is a finite set of translates of `W` covering `X`.
4. **No halvable corner.** The ultraproduct rank restricts to a faithful rank function on each
   `M_d(R)`, and `rk(e) = 2 rk(e)` forces `e = 0`. This is the remark in
   `halvable-corner-makes-elementary-groups-nonsofic`.
