---
rg: 2
id: fpbs-complete-block-free-products-satisfy-identity-e
kind: claim
title: On every free product of finite groups and copies of Z with complete-block generators, every infinite normal subgroup satisfies p_c(N;G) = p^Q_(2->2)(N;G), the relative susceptibility is a quotient Green function, and the Kesten gap holds exactly for nonamenable quotients
distinct_from:
  fpbs-free-product-commuting-quotients-satisfy-identity-e: that proves E on A*H only along normal N containing [A,H]; for finite factors every such Q is a quotient of A x H, hence finite, so it says nothing about infinite quotients of PSL_2(Z) or of any free product of finite groups. This proves E along every infinite normal N, with any number of factors, and no commutation hypothesis.
  fpbs-tree-normal-relative-threshold-is-inverse-cogrowth: that is the one-type tree case (F_d, all blocks lines), where the parameter curve is one-dimensional and radial. This handles several block types, where tau_p is not radial and the matching walk has several independent weights; the new step is an invariance-of-domain argument in weight space. The tree formulas z(s) = s/(1+qs^2), phi(s) = (1-s^2)/(1+qs^2) are recovered as the one-type case of Lemma 1.
  fpbs-percolation-kesten-normal-gap: that conjectures the gap on every Cayley graph; this proves it, together with identity E, on the complete-block free-product class, for every infinite normal subgroup, including quotients that are Kazhdan groups.
  fpbs-tree-products-schreier-kesten-gap-iff-not-co-amenable: that proves the Kesten gap on products of regular trees with an amenable factor via end tilts; the present graphs contain triangles (K_n blocks, n >= 3), have no radial two-point function, and E is proved, not only the gap.
  fpbs-flat-rate-point-exceeds-l2-point-on-free-products: that shows tau_p is NOT proportional to the simple-random-walk Green function G_z at the l2 point on Z/2*Z/2*Z/3; this uses a walk with factor-dependent weights w_i(p), for which tau_p is exactly c_p G up to p_(2->2), for every p and every block type.
  fpbs-relative-threshold-is-quotient-l2-threshold: that is the general open claim E; this settles it on one class and records the mechanism (Theorem B) that any other class would need.
artifacts:
  - experiments/fpbs-complete-block-green-2026-09-17/check_green_representation.py
  - experiments/fpbs-complete-block-green-2026-09-17/output.txt
---

**ESTABLISHED** (agent-verified, not refereed). Proof route:
`fpbs-complete-block-free-products-identity-e-proof`. The route imports
Kesten's two amenability criteria and Brouwer's invariance of domain; nothing
else outside the board.

**Setting.**
- `Gamma = A_1 * ... * A_m`, `m >= 2`. Each factor is either a finite group
  `A_i` of order `n_i >= 2` with generating set `A_i \ {e}` (its Cayley graph is
  the complete graph `K_(n_i)`), or `A_i = Z` with generators `+-1` (a line).
- `G = Cay(Gamma, S)`, `S` the disjoint union of the factor generating sets.
- Exclude `Z/2 * Z/2` (the line); every other such `Gamma` is nonamenable.
- Examples: `PSL_2(Z) = Z/2 * Z/3` with `{s, r, r^2}`; `(Z/2)^{*k} * (Z/3)^{*l}`;
  `F_d` with a free basis; `Z/4 * Z/2` with the `K_4 ⊔ K_2` generators.
- `N` an infinite normal subgroup, `Q = Gamma/N`, `pi` the quotient map.
  `chi^N_p = E_p|K_o ∩ N| = sigma^N_p(e)`, `p_c(N;G) = sup{p : chi^N_p < infinity}`,
  and `p^Q_(2->2)(N;G)` is as in `fpbs-quotient-l2-threshold-sandwich`.

**Block data.** `t_i(p)` is the probability that `e` and a fixed `a in A_i \ {e}`
are connected in Bernoulli(`p`) percolation on the block (`K_(n_i)` or the
line; for the line `t_i = p`, for `K_2` also `t_i = p`, for `K_3`
`t_i = p + p^2 - p^3`). Put

```text
beta_i = (n_i - 1) t_i^2 / (1 + (n_i - 2) t_i)     (complete block),
beta_i = 2 t_i^2 / (1 + t_i^2)                     (line),
B = sum_i beta_i / (1 - beta_i),    c_p = 1/(1 + B),
w_i(p) = t_i / ( D_i (1 - beta_i) (1 + B) ),   D_i = 1 + (n_i - 2) t_i  or  1 + t_i^2,
mu_p = sum_i w_i(p) 1_(A_i \ {e})       (a symmetric finitely supported kernel on Gamma).
```

**Theorem A.** For every such `G` and every infinite normal `N ◁ Gamma`:

1. **(Green representation.)** For `p < p_(2->2)(G)`,
   `tau_p(e, .) = c_p G_(mu_p)` on `Gamma`, where `G_mu = sum_n mu^(*n)`, and
   `||lambda_Gamma(mu_p)|| < 1`. The local identity
   `(delta_e - mu_p) * tau_p(e,.) = c_p delta_e` holds for every `p in [0,1)`.
2. **(Quotient Green function.)** Let `mu-bar_p = pi_* mu_p` and
   `r_Q(p) = ||lambda_Q(mu-bar_p)||`. For `p <= p_c(N;G)`,
   `sigma^N_p = c_p G_(mu-bar_p)` on `Q`; in particular
   `chi^N_p = c_p sum_n mu_p^(*n)(N)`.
3. **(Claim E.)**
   `p_c(N;G) = p^Q_(2->2)(N;G) = min{ p : r_Q(p) = 1 } < p_(2->2)(G)`.
4. **(Percolation Kesten criterion.)** `p_c(G) < p_c(N;G)` iff `Q` is
   nonamenable. If `Q` is nonamenable the pair is of type (i) of C1 in
   `fpbs-relative-threshold-is-quotient-l2-threshold`
   (`||sigma^N_(p_c)||_Q < infinity`); if `Q` is amenable it is of type (iii).
   Type (ii) never occurs on this class.
5. **(At the threshold.)** `chi^N_(p_c(N;G)) = c G_(mu-bar)(e) < infinity` iff
   `mu-bar_(p_c(N;G))` is rho-transient on `Q`.

**Theorem B (the mechanism, class-free).** Let `G = Cay(Gamma,S)`, `N` infinite
normal with `N` nonamenable. Suppose there are an open connected
`Omega ⊂ R^m`, a continuous curve `t: [0,1) -> Omega-bar` with coordinates
strictly increasing in `p`, kernels `kappa_t >= 0` that are coordinatewise
monotone in `t` with `kappa_(t(p)) = tau_p(e,.)`, and a continuous injective
map `W` from `Omega` to symmetric finitely supported kernels in an
`m`-dimensional cone `{sum_i w_i nu_i}` with `(delta - W(t)) * kappa_t = c(t) delta`
and `c > 0`. Suppose also that the representation `kappa_t = c G_(W(t))` holds
on the component of `{||lambda_Gamma(W(t))|| < 1}` that contains the small-`t`
region. Then Claim E holds for `(G,N)`. On other Cayley graphs, the
hypothesis that is hard to meet is the local identity with finitely many free
weights. It asks that the two-point function be the Green function of a
finite-range walk. The block-tree cut vertices give this identity; a graph with
cycles through several blocks does not have it.

**What this changes.**
- The w17 break test asked for E along normal subgroups not containing the
  commutator of the factors. On free products of finite groups, those are all
  the normal subgroups with infinite quotient. Here E holds along all of them,
  with no exception.
  In particular E and the percolation Kesten gap hold on `PSL_2(Z)` with
  `{s, r, r^2}` along the kernel of every map onto an infinite
  `(2,3)`-generated group. Those groups include infinite Kazhdan groups:
  results of Tamburini and coauthors give (2,3)-generation for `SL_n(Z)` with
  `n` large. That reference was not checked here.
- On this class `p_c(N;G)` is always a spectral threshold of an explicit walk
  on `Q`. So no pair has type (ii), and the C1 invariant `||sigma^N_(p_c)||_Q`
  decides the gap. This agrees with C1 of the target claim.
- The obstruction for a general graph is named in Theorem B: Green
  representability of `tau_p` along a finite-dimensional family.
  The positivity and variational facts of
  `fpbs-amenable-normal-fibre-mass-bound-2026-09-16` are softer consequences,
  and by themselves they do not force E.
- **Does not advance the flagship directly.** Every graph in the class has
  infinitely many ends, so `p_u = 1` and `p_c < p_u` was already known.

**Numerical check.** The artifact script checks the following.
- The local identity to `2e-16`, on balls of radius 6, for five block
  configurations and `p in {0.15, 0.3, 0.5, 0.9}`.
- The `l1` relation `||mu_p||_1 = 1 - c_p/chi_p`.
- `tau = c G_mu` at `p = 0.1`, by truncated Neumann series.
- On `T_3 = (Z/2)^{*3}`, `w(p) = p/(1+2p^2)` peaks exactly at
  `p_(2->2) = 1/sqrt 2`, where `||lambda(mu_p)|| = 1`.
