---
rg: 2
id: promislow-inverse-has-equal-dihedral-syllable-length
kind: claim
title: A unit of K[P] and its inverse have the same syllable length in every dihedral quotient of the Promislow group
distinct_from:
  promislow-radius4-one-sided-and-integral-separation: that counts the units of F_2[P] supported in B(4), and its proof uses this symmetry to put their inverses in one 155-element box; this is the symmetry itself, over every field and for every support.
---

Let `P` be the Promislow group in the affine model
`(s, t)(s', t') = (ss', t + s t')`, with `a = ((1,-1,-1),(1,1,0))` and
`b = ((-1,1,-1),(0,1,1))`. For `i = 0, 1, 2` let
`pi_i : P -> D_infty = Z x| Z/2` be `pi_i(s, t) = (t_i, [s_i = -1])`, with
kernel `N_i`. For `m in Z` the involutions `r_m = (m, 1)` and
`r_(m+1) = (m+1, 1)` generate `D_infty = <r_m> * <r_(m+1)>`. Write
`l_i^m(g)` for the length of the alternating word in `r_m, r_(m+1)` that
represents `pi_i(g)`:

```text
l_i^m(g) = 2|n|                             if pi_i(g) = (n, 0),
l_i^m(g) = min(2|m-j| + 1, 2|m+1-j| + 1)    if pi_i(g) = (j, 1),
```

and `L_i^m(alpha)` for the maximum of `l_i^m` over `supp(alpha)`.

**ESTABLISHED.** Let `K` be any field, `i in {0, 1, 2}` and `m in Z`. If
`sigma, tau` are nonzero elements of `K[P]` with `sigma tau in K[N_i]`, then
`L_i^m(sigma) = L_i^m(tau)`. In particular `L_i^m(u^(-1)) = L_i^m(u)` for
every unit `u`.

So a unit supported in a finite set `S` has its inverse supported in

```text
box(S) = { g in P : l_i^m(g) <= max_(h in S) l_i^m(h) for all i and m },
```

and intersecting over finitely many pairs `(i, m)` gives a finite superset
of `box(S)`. Tabei's 155-element box is built the same way for the whole
ball `B(4)`.

DERIVATION
[[craven-pappas-dihedral-length-symmetry-citation]]
