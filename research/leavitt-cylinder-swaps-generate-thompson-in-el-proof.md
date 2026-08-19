---
rg: 2
id: leavitt-cylinder-swaps-generate-thompson-in-el-proof
kind: route
title: The characteristic-two triple product, the same-leaf transposition identity, and one refinement
target: leavitt-cylinder-swaps-generate-thompson-in-el
requires: []
artifacts:
  - c1168433:official/counterexample.tex
---

## Why sufficient

A complete direct computation in `R = L_(F_2)(1,2)`; no approximation
property, no external theorem beyond the fact that cylinder swaps generate
`V` (Bleak--Quick, arXiv:1511.02123, Theorem 1.1).

**The prefix-code identities.**  Incomparability of the words of `E` gives
`t_(a_i) s_(a_j) = delta_(ij)` and
`(s_(a_i) t_(a_j))(s_(a_k) t_(a_l)) = delta_(jk) s_(a_i) t_(a_l)`, and the
Leavitt relation gives `e_a = e_(a0) + e_(a1)`, hence `e_E = 1` for a complete
code.  These are what make `Theta_E : M_q(R) -> e_E R e_E` a ring isomorphism
and `(1 - e_E) + Theta_E(I_q + r E_(ij)) = 1 + s_(a_i) r t_(a_j)` an
elementary root extended by the identity off the code.

**Different leaves.**  With `P = s_rho t_sigma`, `Q = s_sigma t_rho` for
`rho = a_i w`, `sigma = a_j w'` and `i /= j`, we have `P^2 = Q^2 = 0`,
`PQ = e_rho`, `QP = e_sigma`, so expanding `(1+P)(1+Q)(1+P)` gives
`1 + 2P + Q + e_rho + e_sigma + PQP`; then `PQP = e_rho P = P` and `2P = 0`
leave `1 + P + Q + e_rho + e_sigma`, which is `tau_(rho,sigma)`.  Both factors are elementary `E`-roots because
`P = s_(a_i)(s_w t_(w'))t_(a_j)` with `i /= j`.

**Same leaf.**  `tau_(rho,sigma) = tau_(rho,a_j) tau_(sigma,a_j)
tau_(rho,a_j)` for any leaf `a_j` different from the common one; each factor
is covered by the previous paragraph.  This needs `q >= 2`.

**Refinement.**  `s_b t_a = s_(b0) t_(a0) + s_(b1) t_(a1)` says a prefix
table may be refined without changing the unit it names, and disjointly
supported swaps commute, so `tau_(rho,sigma) = prod_(w in {0,1}^k)
tau_(rho w, sigma w)` for any `k`.  Choosing `k` large enough that every
`rho w` and `sigma w` extends a leaf of `D` puts every generator of `V` in
`EL_D(R)`.

**The small copies.**  Running the same-leaf argument with `E = alpha` puts
every cylinder swap supported inside `[l]`, `l` extending some `alpha_i`, in
`EL_alpha(R)`; those swaps generate `V_l`.

## Not a restatement of the ambient membership

The second half is not a special case of the first: `alpha` is **not** a
complete code, so `EL_alpha(R)` is a corner group extended by the identity,
and the refinement trick is unavailable there.  What replaces it is that all
the words involved already extend one leaf, which is the hypothesis the
same-leaf identity wants.
