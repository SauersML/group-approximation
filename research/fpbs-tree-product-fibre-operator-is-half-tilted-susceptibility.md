---
rg: 2
id: fpbs-tree-product-fibre-operator-is-half-tilted-susceptibility
kind: claim
title: On a tree times any Cayley graph, the fibre-summed operator over the tree factor has norm equal to the half-tilted susceptibility, so every such pair is critical fibre l2 and Claim E becomes a fibre square-root law
distinct_from:
  fpbs-relative-threshold-is-quotient-l2-threshold: that is the open identity p_c(N;G) = p^Q_(2->2)(N;G) on every pair and names F_2 x F_2 as its test case; this proves the pair is never of type (ii) when the quotient factor is a tree, computes p^Q_(2->2) = p_t exactly there, and reduces the identity on those graphs to one fibre summability condition, without proving it.
  fpbs-quotient-l2-threshold-sandwich: that proves the general sandwich p_c <= p^Q_(2->2) <= min{p_(2->2), p_c(N;G)}; this evaluates the middle term exactly on T x H as the tiltability threshold of the end-fixing group, which makes the left inequality strict.
  fpbs-hutchcroft-pan-tree-times-amenable-l2-threshold-is-pu: that imports p_(2->2) = p_u on T x H for amenable H; this treats arbitrary H, and identifies the fibre operator along H, not the two-point operator, with chi_(p,1/2).
  fpbs-tree-projected-square-root-fibre-law-below-pu: that is an open l^(2+) hitting-probability law below p_u over an amenable kernel with free quotient; this proves an operator identity valid for every H and every p, and its reformulation of Claim E uses the relative threshold p_c(N;G), which differs from p_u when H is nonamenable.
  fpbs-boundary-tilted-susceptibility-kernel: that builds tilted mass transport on quasi-invariant boundaries of general Cayley graphs; this uses only the end of the tree factor of a product, and proves an equality of the tilted susceptibility with a quotient operator norm.
  fpbs-hyperbolic-nonunimodular-critical-l2-gap: that imports p_c < p_(2->2) for nonunimodular graphs; this derives the stronger fibre statement ||sigma^N_(p_c)||_Q < infinity along the second factor, which that import does not give.
  fpbs-percolation-kesten-normal-gap: that asks for p_c < p_c(N;G) for every normal N with nonamenable quotient on every generating set; this proves it only for N = H in Lambda x H with product generators and a tree Cayley graph on Lambda.
  fpbs-product-fibre-collision-loss-vanishes: that is an open asymptotic inequality for a nonamenable factor times a high-degree factor; this is an exact identity on tree products and needs no degree asymptotics.
artifacts:
  - experiments/fpbs-tree-product-fibre-tilt-2026-09-17/check_fibre_tilt.py
  - experiments/fpbs-tree-product-fibre-tilt-2026-09-17/check_fibre_tilt.out
---

**ESTABLISHED.** Proof route:
`fpbs-tree-product-fibre-operator-half-tilt-proof`.

**Setting.**

- `Lambda` is a finitely generated group and `S_Lambda` a finite symmetric
  generating set such that `Cay(Lambda,S_Lambda)` is the `k`-regular tree
  `T`, with `k >= 3`. Examples are `(Z/2)^{*k}` on its involutions, and `F_r`
  on a free basis with `k = 2r`.
- `H_grp` is any infinite finitely generated group, and `S_H` any finite
  symmetric generating set. Put `H = Cay(H_grp,S_H)`.
- `Gamma = Lambda x H_grp` with `S = S_Lambda ⊔ S_H`. Then `G = Cay(Gamma,S)`
  is the Cartesian product `T x H`.
- `N = {1} x H_grp` is normal and `Q = Gamma/N = Lambda`. The fibre over
  `v in Lambda` is `{v} x H_grp`.
- `sigma_p(v) = sum_(y in H_grp) tau_p(o,(v,y))` is the fibre-summed kernel,
  and `||sigma_p||_Q` is as in `fpbs-quotient-l2-threshold-sandwich`.
  `p^Q_(2->2)(N;G) = sup{p : ||sigma_p||_Q < infinity}`.
- Fix an end `xi` of `T`. `Gamma_xi = Aut_xi(T) x H_grp` acts on `G` by
  automorphisms and is transitive and nonunimodular. `chi_(p,1/2)` and
  `p_t = p_t(G,Gamma_xi)` are Hutchcroft's half-tilted susceptibility and
  tiltability threshold (`fpbs-hutchcroft-nonunimodular-pc-below-pt`).
- `f_p(n) = sigma_p(v)` for any `v` with `|v| = n`. The proof shows that this
  depends only on `n`. It is the expected size of the intersection of `K_o`
  with one fibre at tree distance `n`.

**Theorem.**

1. **(Fibre operator = half-tilted susceptibility.)** For every `p in [0,1]`,
   as an identity in `[0,infinity]`,

   ```text
   ||sigma_p||_Q = chi_(p,1/2)
                 = f_p(0) + sum_(n>=1) f_p(n) (k-1)^(n/2) (2 + (n-1)(k-2)/(k-1)).
   ```

   Hence `p^Q_(2->2)(N;G) = p_t(G,Gamma_xi)`. Equivalently,
   `p^Q_(2->2)(N;G) = sup{p : sum_n (n+1)(k-1)^(n/2) f_p(n) < infinity}`.
2. **(Every such pair is of type (i).)** `||sigma_(p_c)||_Q < infinity`. So

   ```text
   p_c(G) < p_t(G,Gamma_xi) = p^Q_(2->2)(N;G) <= min{ p_(2->2)(G), p_c(N;G) }.
   ```

   In particular:
   - the percolation Kesten gap `p_c(G) < p_c(N;G)` holds along `N = H`, for
     every `H`;
   - the weak form `E'(G,N)` of `fpbs-relative-threshold-is-quotient-l2-threshold`
     holds;
   - no pair of this form is of type (ii) in C1 of that node.

   This covers the named test case `F_2 x F_2` with its standard product
   generating set, `T_4 x T_4`, along either factor. It is type (i).
3. **(Claim E on tree products.)**
   - `p_c(N;G) = sup{p : f_p(0) < infinity}`.
   - `E(G,N)` holds iff `p_c(N;G) <= p_t(G,Gamma_xi)`. This is iff the
     **fibre square-root law** holds:

     ```text
     for every p < p_c(N;G):   sum_(n>=1) n (k-1)^(n/2) f_p(n) < infinity.
     ```

   - If `H_grp` is amenable, `E(G,N)` holds, and
     `p_t = p^Q_(2->2) = p_(2->2) = p_c(N;G) = p_u`.
   - So a counterexample to Claim E of this form needs `H_grp` nonamenable and
     some `p` with `p_t < p < p_c(N;G)`. Such a `p` lies strictly above
     `p_c(G)`.

The fibre square-root law for nonamenable `H` is the open node
`fpbs-tree-product-fibre-square-root-law-below-relative-threshold`.

**What this changes.**

- The escape named in `fpbs-relative-threshold-is-quotient-l2-threshold` was a
  type-(ii) pair: a relative gap without critical fibre l2. The proposed test
  case `F_2 x F_2` is not one. On every tree product with product generators,
  the relative gap is critical fibre l2, and it is supplied by
  nonunimodularity. So on these graphs the obstruction C1 does not bite, and
  the only open part of Claim E is the upper identification of `p_c(N;G)`.
- The quotient l2 threshold, defined through the unimodular group `Gamma`,
  equals a threshold of the nonunimodular group `Gamma_xi`. The half-tilt
  `lambda = 1/2` is forced: the Schur weight `(k-1)^(h/2)` is the positive
  `rho`-eigenfunction of the tree adjacency operator that realises `||A||`.

**Checks.** The script in `artifacts` verifies the following.

- `A g = 2 sqrt(k-1) g` and `sum_(|v|=n) g(v) = P_n(2 sqrt(k-1))`, against
  the closed form, for `k = 3..6` and `n <= 7`, on reduced words.
- The degenerate case `H` = point, where `sigma_p(v) = p^|v|` and the formula
  gives `p_t = (k-1)^(-1/2) = p_(2->2)(T)`.
