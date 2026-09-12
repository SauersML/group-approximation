---
rg: 2
id: orthogonal-heisenberg-self-copy-microstate-proof
kind: route
title: Extend the two coordinate injections to permutations on each finite window
target: orthogonal-heisenberg-self-copy-skeleton-has-marked-microstates
requires:
  - finite-tags-do-not-atomize-heisenberg-schrodinger-tower
---

The coordinate ranges of `f_0` and `f_1` are the even and odd coordinate
subspaces.  Orthogonality of these ranges proves the central-product
statements, and together they span `V`.  Britton's lemma for each successive
HNN extension embeds the vertex group `H(V)` into `Gamma`; hence `Z` remains
nontrivial.

Fix a finite set of relations from `(OHS2)`.  Only finitely many base-group
elements occur, so their coefficients and the coefficients of their two
images are supported on the first `2L` coordinates for some `L`.  Choose
`M>=2L`.  Each injection

```text
{0,...,L-1} -> {0,...,M-1},       n |-> 2n+i
```

extends independently to a permutation `sigma_(i,M)` of the full coordinate
set.  On the Schrödinger space `l2(F_p^M)`, simultaneous permutation of the
position and momentum coordinates is implemented by the basis-permutation
unitary

```text
U_(i,M) delta_x=delta_(sigma_(i,M) x).
```

It conjugates `X(e_n)` and `Y(e_n)` to the corresponding `2n+i` root
operators for every `n<L`, and it fixes the scalar central operator
`zeta I`.  The finite Heisenberg multiplication table and every requested
HNN covariance relation are therefore exact.

For a sequence of growing finite relation sets, choose `L` and then `M` at
each stage as above.  Evaluating fixed representatives of group elements in
these generator matrices gives a presentation microstate: every fixed group
identity has a finite derivation and is therefore exact from some stage on.
The marked word always has

```text
||zeta I-I||_2=|zeta-1|>0.
```
