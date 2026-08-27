---
rg: 2
id: atlas-cfsg-family-split-does-not-finitize-a8-carriers
kind: claim
title: A CFSG family split does not reduce Atlas A8 carriers to a finite census
distinct_from:
  atlas-natural-a8-supports-collapse-before-collision: that uniformly excludes one infinite family of marked pairs by a support theorem; this explains why the remaining CFSG families do not become a finite list merely by naming them.
  atlas-fixed-packet-arithmetic-has-no-hs-gap: that concerns normalized multiplicity arithmetic in matrix packets; this is an exact finite-group carrier obstruction.
---

Partitioning finite simple groups into alternating, classical, exceptional,
and sporadic families does **not** turn the finite-simple Atlas escape problem
into a finite list of `A8` carriers.

Already in defining characteristic two there is an infinite classical tower.
Use the exceptional isomorphism

```text
A8 ~= SL4(2).
```

For every `m>=2`, the repeated block representation

```text
g |-> diag(g,...,g) in SL_(4m)(2)                   (CF8-1)
```

is injective.  Since the scalar center over `F2` is trivial, it embeds `A8`
in the finite simple group `PSL_(4m)(2)`.  Thus both the ambient rank and the
multiplicity of the natural four-dimensional `A8` module are unbounded.

Likewise, the alternating branch contains natural-support copies in every
`A_n`, `n>=8`; Cairn excludes that particular infinite family only because
the packet supplies the stronger support containment theorem
`atlas-natural-a8-supports-collapse-before-collision`, not because CFSG made
the carrier list finite.

Consequently a terminal familywise proof must add a relation-sensitive
statement of one of the following forms:

1. packet plus collision forces both charts into one proper common carrier;
2. a representation-independent support/module invariant excludes every
   multiplicity and rank at once; or
3. all surviving embeddings reduce to finitely many marked module seams by
   a theorem stronger than the bare CFSG/Aschbacher family partition.

An order-by-order sieve cannot be replaced merely by the phrase
"alternating/classical/exceptional/sporadic."
