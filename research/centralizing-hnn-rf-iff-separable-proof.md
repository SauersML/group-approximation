---
rg: 2
id: centralizing-hnn-rf-iff-separable-proof
kind: route
title: Push a Britton-reduced word into a graph of finite groups, and read closure points off the pullback of the edge image
target: centralizing-hnn-is-residually-finite-iff-edge-is-separable
requires: []
---

Throughout, `Gamma = K *_L (L x Z)` is an HNN extension of `K` with both
associated subgroups equal to `L` and the identity isomorphism, so
Britton's lemma applies: a word `g = f_0 v^{e_1} f_1 ... v^{e_m} f_m` with
`f_i notin L` at every pinch position is nontrivial.

**Separable implies residually finite.**  Let `g != 1` be Britton-reduced
as above.  Since `L` is closed and `f_i notin L` at the pinches, there is
a finite-index normal `N <= K` with `f_i notin L N` for those finitely
many `i` (and `f_0 notin N` when `m = 0`); let `q : K -> Q = K/N` and
`H = q(L)`, so `q(f_i) notin H`.  The relations `[v, L] = 1` are respected
by `q`, so `q` extends to

```text
Gamma -> Q *_H (H x Z),
```

and the image of `g` is Britton-reduced there, hence nontrivial.  The
target is the fundamental group of a finite graph of groups with finite
vertex group `Q` and virtually cyclic vertex group `H x Z` amalgamated
over the finite group `H`, hence virtually free and in particular
residually finite.  So a finite quotient of `Gamma` separates `g` from
the identity.

**Residually finite implies separable.**  Let `k` lie in the profinite
closure of `L` in `K`, i.e. in every finite-index subgroup of `K`
containing `L`, and suppose `k notin L`.  Then `[v, k] != 1` in `Gamma` by
Britton.  Let `chi : Gamma -> P` be any homomorphism to a finite group and
put

```text
U = { f in K : chi(f) in chi(L) }.
```

`U` is a subgroup of `K` containing `L`, and it has finite index because
it is a union of preimages of finitely many cosets.  Hence `k in U`, so
`chi(k) = chi(l)` for some `l in L`; since `chi(v)` commutes with
`chi(L)`, it commutes with `chi(k)`, and `chi([v, k]) = 1`.  As `chi` was
arbitrary, `Gamma` is not residually finite.
