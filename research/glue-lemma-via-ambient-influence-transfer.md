---
rg: 2
id: glue-lemma-via-ambient-influence-transfer
kind: route
title: Dead -- read the bounded label list off the ambient influential coordinates
target: affine-orientation-glue-lemma
requires: []
---

**Dead.**  Recorded because it is the first thing anyone tries, and because
the reason it fails is the most informative fact in the region.

The attack: a coset `C_b` that is `(d, delta)`-heavy for the restriction
`g|_{D_b}` should owe its heaviness to an ambient coordinate of `g` that is
itself low-degree influential.  Collect the ambient influential
coordinates, of which there are boundedly many by the standard
`sum_i Inf^{<=d}_i(g) <= d` budget, and take that set as `Q`.  The
`gamma`-fraction conclusion follows because a heavy coset must contain one
of them.

It is killed by `linear-pairing-memorizer-restricts-to-a-dictator`.  The
memorizer `B_{b,r}` is bounded by 1, is homogeneous of degree `2r+1` so
noise multiplies it by the constant `rho^(2r+1)` and damps nothing, and
restricts on `D_b` to an exact dictator -- while **every** ambient
low-degree influence is `Theta_r(N^{-r})`.  The set of ambient influential
coordinates is empty at any fixed threshold, and yet the restricted
heaviness is full.  So the implication the attack rests on is false, with a
counterexample that satisfies every hypothesis one would think to add.

What survives the kill: the conclusion of the glue lemma itself, since
`Q = {0}` still works for a single direction.  The obstruction is to the
*derivation*, not to the statement.  See
`glue-lemma-via-parseval-budget-across-directions` for the natural
strengthening, which dies too.
