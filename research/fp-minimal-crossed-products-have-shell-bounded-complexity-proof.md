---
rg: 2
id: fp-minimal-crossed-products-have-shell-bounded-complexity-proof
kind: route
title: Count patterns through their shells, using two-sided Følner sets and bounded shells of two-ended groups
target: fp-minimal-crossed-products-have-shell-bounded-complexity
requires: [fp-minimal-crossed-products-have-no-homoclinic-pairs]
artifacts:
  - research/artifacts/fp-minimal-crossed-products-homoclinic-kill-2026-09-17.md
---

This is Corollaries 4–7 of the artifact.

1. **Shell bound.** By `fp-minimal-crossed-products-have-no-homoclinic-pairs`, the pattern of a point on
   `F` is a function of its pattern on `N_r(F) \ F`. So
   `|L_F(X)| <= |L_(N_r(F) \ F)(X)| <= |A|^(|N_r(F) \ F|)`.
2. **Amenable.** `P × P` is amenable and acts on `P` by `(g,h)·q = g q h^(-1)`, so there are finite
   `F_n` that are left Følner and satisfy `|F_n B_r \ F_n| / |F_n| -> 0`. Pattern counts are
   left-translation invariant, so by Ornstein-Weiss `h_top(X) = lim log|L_(F_n)| / |F_n|`. By Step 1
   this is `<= lim |F_n B_r \ F_n| log|A| / |F_n| = 0`.
3. **Virtually cyclic.** `P` is infinite, so it has `<c>` of finite index `m` with right cosets
   `<c> g_j`. The sets `F_n = {c^i g_j : |i| <= n}` exhaust `P`, and `F_n B_r ⊆ {c^i g_j : |i| <= n + C_r}`,
   so the shells have size `<= 2 m C_r`. By Step 1, `|L_(F_n)(X)|` is bounded independently of `n`, so `X`
   is finite. This contradicts the hypothesis, so no finitely presented crossed product exists.
4. **`Z^d`.** `|N_r(B_N) \ B_N| <= C' N^(d-1)`, so Step 1 gives `log|L_(B_N)| <= C' log|A| N^(d-1)`. `∎`
