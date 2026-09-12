---
rg: 2
id: repeated-ldpc-private-matching-proof
kind: route
title: Sparsify two good code-column measures by random perfect matchings
target: repeated-good-ldpc-coordinates-give-private-weyl-sampler
requires:
  - generator-column-pauli-test-globalizes-but-does-not-pin-sites
  - full-weyl-energy-support-floor
---

Write `mu_r,nu_r` for the uniform coordinate-functional measures of the two
base codes.  Relative distance `delta` is exactly the statement that every
nontrivial character has `mu_r`- and `nu_r`-mass at least `delta` on its
negative set.  Hence the inverse Poincare constants of both column measures
are uniformly bounded.  The generator-column transfer followed by
`full-weyl-energy-support-floor` gives a universal lower bound `eta_0>0` for
the full `mu_r times nu_r` Weyl energy of every exact additive pair in
dimension `d<=r`.

Repeating coordinates does not change either measure.  Choose a uniform
perfect matching between the two N-element repeated multisets.  For one
fixed representation, its matched energy is the average of a bounded
`N by N` loss matrix along a random permutation.  The permutation exposure
martingale (or transposition bounded differences) gives

```text
Pr[matched energy < eta_0/2] <= exp(-c N).                  (RLP1)
```

As in the private Weyl metric-entropy proof, exact additive pairs in every
`d<=r` are covered by `exp(O(r^2))` character-list/unitary net points, and
the loss is uniformly Lipschitz in the relative unitary.  Since
`N=A Theta(r^2)`, choosing `A` large makes `(RLP1)` survive the union bound.

For the class-two overlay, let `v,w` be independent coordinate functionals
from one base code and let `beta` be a nonzero alternating form.  Its radical
has codimension at least two.  Choose a nonzero linear functional vanishing
on the radical.  Code distance gives

```text
Pr[v notin rad(beta)] >=delta.
```

For every such `v`, the nonzero functional `w -> beta(v,w)` is one on at
least `delta` of the coordinate measure.  Therefore

```text
Pr[beta(v,w)=1] >=delta^2.                                 (RLP2)
```

A random perfect matching within the repeated coordinates concentrates
around `(RLP2)` with tail `exp(-c_delta N)`.  Union-bound over the fewer than
`2^(r(r-1)/2)` alternating forms, again increasing `A` if necessary.  This
gives a fixed matching with a uniform exterior-square gap.

All scalar code assertions follow directly: replicated parity checks make
each layer a codeword, and exact expander equalities identify the layers.
The bounded-degree and positive-port-density statements are literal counts.
Finally, goodness of a proposed finite pair of matchings is decidable: the
exterior condition is finite, while the matrix Weyl condition is the same
real-closed-field sentence used in recursive private-sampler selection.
