---
rg: 2
id: fpbs-tree-cayley-graphs-satisfy-identity-e
kind: claim
title: On every Cayley graph that is a regular tree, every infinite normal subgroup satisfies p_c(N;T) = p^Q_(2->2)(N;T), and the fibre kernel is an explicit resolvent of the quotient walk
distinct_from:
  fpbs-relative-threshold-is-quotient-l2-threshold: that asserts the identity on every pair and is OPEN; this proves it on every tree Cayley graph, for every infinite normal subgroup, which turns item 2 of its Evidence (a sketch on free groups) into a theorem and extends it to free products of copies of Z and Z/2.
  fpbs-tree-normal-relative-threshold-is-inverse-cogrowth: that computes p_c(N;T) and chi^N_p = sigma_p(e) on the free-group tree; this computes the whole fibre kernel sigma_p on the quotient and its l2(Q) operator norm, and derives p_c(N;T) independently of that node's branching-process argument.
  fpbs-free-product-commuting-quotients-satisfy-identity-e: that proves E on A * H for normal N containing [A,H]; this allows every infinite normal N, including those not containing [A,H], but only when the Cayley graph is a tree (factors Z or Z/2 with their standard generators).
---

**ESTABLISHED.** Proof in `fpbs-tree-cayley-graphs-identity-e-proof`.

**Setting.**

- `Gamma` is a group and `S` a finite symmetric generating set with
  `e ∉ S` such that `T = Cay(Gamma,S)` is the `(q+1)`-regular tree, `q >= 2`.
  Examples are `F_d` on a free basis (`q = 2d-1`), `(Z/2)^{*b}` on its
  involutions (`q = b-1`), and every mixed free product `Z^{*a} * (Z/2)^{*b}`
  on its standard generators (`q = 2a+b-1`).
- `N` is an infinite normal subgroup, `Q = Gamma/N`, `pi: Gamma -> Q`.
- `mu` is the uniform probability measure on `S`, `mu_Q = pi_* mu`,
  `rho_Q = ||lambda_Q(mu_Q)|| = limsup_k mu_Q^(*k)(e)^(1/k)`, and
  `G_Q(w) = sum_k w^k mu_Q^(*k)(e)`.
- `z(s) = s/(1+q s^2)`, `w(s) = (q+1) z(s)`, `phi(s) = (1-s^2)/(1+q s^2)`.
- `sigma_p(u) = sum_(x in u) tau_p(o,x)` for `u in Q`, `||.||_Q` and
  `p^Q_(2->2)(N;T)` as in `fpbs-quotient-l2-threshold-sandwich`.

**Theorem.**

1. **(Resolvent form.)** For `0 <= p <= 1/sqrt q`, pointwise on `Q` and in
   `[0,infinity]`,

   ```text
   sigma_p = phi(p) sum_(k>=0) w(p)^k mu_Q^(*k).
   ```

2. **(Norm.)** `rho_Q > 2 sqrt q/(q+1)`, so there is a unique
   `s_N in (0, 1/sqrt q)` with `w(s_N) rho_Q = 1`. For `p < s_N`,

   ```text
   ||sigma_p||_Q = phi(p) / (1 - w(p) rho_Q) < infinity,
   ```

   and `||sigma_p||_Q = infinity` for `p >= s_N`.
3. **(Identity E.)** `p_c(N;T) = p^Q_(2->2)(N;T) = s_N`.
4. **(Type.)** `p_c(T) = 1/q` and `w(1/q) = 1`. So the pair is of type (i) of
   C1 in `fpbs-relative-threshold-is-quotient-l2-threshold` iff `rho_Q < 1`,
   that is, iff `Q` is nonamenable. It is of type (iii) iff `Q` is amenable.
   No tree pair is of type (ii).
5. **(Endpoint.)** `chi^N_(s_N) = sigma_(s_N)(e) = phi(s_N) G_Q(1/rho_Q)`,
   finite iff `mu_Q` is rho-transient, while `||sigma_(s_N)||_Q = infinity`
   in all cases. Together with item 2, the norm blows up like
   `(s_N - p)^(-1)`, the rate forced by part 5 of the sandwich.

**What it settles.**

- Item 2 of the Evidence of `fpbs-relative-threshold-is-quotient-l2-threshold`
  was a sketch; it is now a proof, and it covers every infinite normal
  subgroup of every tree Cayley graph, not only those of `F_d`.
- The w17 next test "normal subgroups of `A * H` not containing `[A,H]`" is
  answered positively when `A, H` are `Z` or `Z/2` with standard generators.
  There the fibre sum is an alternating word sum in two non-commuting kernels,
  and it is still a resolvent. The reason is not a renewal at cut vertices
  over commuting images. It is the pointwise tree identity
  `s^|x| = phi(s) G_(w(s))(e,x)`, which makes `tau_p` itself a Green function
  on `Gamma`, before any quotient is taken.
- **Invariant.** Green representability of `tau_p` on `Gamma`:
  `tau_p = c(p) sum_k w(p)^k nu^(*k)` for one symmetric probability `nu` on
  `Gamma`, for every `p` up to `p^Q_(2->2)`. Every quotient then inherits a
  resolvent, and E follows with no further input. A type-(ii) pair therefore
  needs a graph on which `tau_p` is not a Green function of any single walk
  on `Gamma` in the window `(p_c, p_c(N;G))`.
