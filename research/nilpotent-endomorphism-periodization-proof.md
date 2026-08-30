---
rg: 2
id: nilpotent-endomorphism-periodization-proof
kind: route
title: Extend nilpotent branches to one pro-p completion
target: nilpotent-endomorphism-families-have-periodizations
requires: []
---

An injective endomorphism has image isomorphic to `Gamma`, hence of full
Hirsch length.  Such a subgroup of a finitely generated nilpotent group has
finite index.  Its image in the abelianization is therefore finite index, so
the induced matrix on the torsion-free part of `Gamma_ab` has nonzero
determinant.

Choose a residual prime `p` avoiding the torsion of `Gamma_ab` and all these
determinants.  The embedding of `Gamma` into its pro-`p` completion `P`
retains `y`.  Every endomorphism extends continuously and acts invertibly on

```text
P/Frat(P)=H_1(Gamma;F_p).
```

By the pro-`p` Burnside basis theorem and Hopficity, each extension is an
automorphism.  Given an open normal `U` not containing `y`, intersect all
open subgroups of index at most `[P:U]`.  The resulting subgroup `C` is open,
characteristic, and contained in `U`.  Thus the finite `p`-group `Q=P/C`
detects `y` and is simultaneously invariant under every branch.  Sending
each stable letter to its induced automorphism of `Q` gives the asserted
finite marked semidirect-product quotient.
