---
rg: 2
id: relator-only-hs-obstruction-has-trivial-model
kind: claim
title: Relator-only normalized-HS obstructions cannot rule out microstates
invalidates: [nonhyperlinear-from-extensive-index-defect]
distinct_from:
  additive-index-instability: That is an amplification no-go for raw additive indices; this is the more elementary logical gate that a finite presentation always has the trivial exact unitary tuple, so relator defect alone cannot obstruct existence of approximate representations.
  index-density-is-amplification-stable: That says index per dimension survives amplification; this says amplification-stability is irrelevant until a separation condition ties the index to a nontrivial group element.
---

Let

```text
P = < S | R >
```

be any finite group presentation.  For every matrix dimension `d>=1`, the
assignment

```text
s |-> 1_d   (s in S)
```

satisfies every relator in `R` exactly.  Hence every normalized-Hilbert--Schmidt
relator defect of this tuple is zero.

Consequently no condition quantified over **all** unitary `S`-tuples and
triggered only by small relator defect can, by itself, prove that the presented
group is nonhyperlinear.  Any such condition has to be compatible with the
trivial exact tuple.  To obstruct hyperlinearity one must additionally consume
what distinguishes a hyperlinear embedding from the trivial homomorphism: for
example a marked word `z!=1` required to stay a fixed `L2` distance from the
identity, or the regular-character trace conditions on a finite window.

In particular, a positive-density topological/index syndrome is useful for the
nonhyperlinear programme only after two extra pieces are present:

1. **marked forcing:** separation of a nontrivial word forces a positive
   density of syndrome; and
2. **energy payment:** that syndrome forces a positive normalized-HS relator
   cost (or some other quantity that must tend to zero in a hyperlinear
   microstate).

A topological index that merely obstructs perturbation to an exact
representation is not enough: hyperlinearity asks only for increasingly good
approximate representations, not for stability/repair of them.
