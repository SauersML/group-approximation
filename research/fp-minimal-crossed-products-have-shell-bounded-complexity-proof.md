---
rg: 2
id: fp-minimal-crossed-products-have-shell-bounded-complexity-proof
kind: route
title: Count patterns through their shells, using two-sided Følner sets and bounded shells of two-ended groups
target: fp-minimal-crossed-products-have-shell-bounded-complexity
requires: [fp-minimal-crossed-products-have-no-homoclinic-pairs, fp-minimal-crossed-product-patterns-fill-width-r-shells]
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

**2026-09-18, referee: Step 1 is off by a factor of two in the shell width.** Item 2 of
`fp-minimal-crossed-products-have-no-homoclinic-pairs`, and Corollaries 3 and 4 of the
artifact, are proved only with the width-`2r` shell: an `r`-window is a ball `p B_r`, so one
that meets `F` at `f` satisfies `p ∈ f B_r` and lies in `f B_(2r) ⊆ N_(2r)(F)`, not in
`N_r(F)`. So what Step 1 gives is `|L_F(X)| <= |A|^(|N_(2r)(F) \ F|)`, and part 1 of the
target, stated at width `r`, needs the added prerequisite
`fp-minimal-crossed-product-patterns-fill-width-r-shells`. Parts 2, 3 and 4 go through
verbatim after substituting `2r` for `r`, since Steps 2-4 need only that the shell is
`o(|F_n|)`, bounded, or `O(N^(d-1))`; in Step 3, `F_n B_(2r) ⊆ {c^i g_j : |i| <= n + C_(2r)}`
still gives shells of size `<= 2 m C_(2r)`, so `|X| <= |A|^C` and `X` is finite. (Step 2's
justification "an amenable group acting on a set admits Følner sets for that action" is not a
valid general principle, but the fact it needs — every amenable group has two-sided Følner
sequences — is standard, so that is a loose citation and not a gap.)
