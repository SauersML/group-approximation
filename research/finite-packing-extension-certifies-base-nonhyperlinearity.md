---
rg: 2
id: finite-packing-extension-certifies-base-nonhyperlinearity
kind: claim
title: A successful finite packing extension already certifies nonhyperlinearity of its base
root: true
artifacts:
  - research/finite-packing-extension-certifies-base-nonhyperlinearity-proof.md
distinct_from:
  finite-packing-preserves-hyperlinearity: that proves the permanence fence; this combines it with the packing contradiction and identifies the base, rather than the auxiliary amalgam, as the actual witness.
  simultaneous-character-packing-removes-max-loss: that proves one sharp packing contradiction for an extended presentation; this descends any such contradiction to the original contextual base.
---

Let `Gamma` be a contextual base group and form `Gamma_hat` by attaching
finitely many finite overgroups along finite context subgroups.  If a
character-packing argument proves that `Gamma_hat` is nonhyperlinear, then

```text
Gamma is nonhyperlinear.                                  (FPB1)
```

In particular, any finite-overgroup packing which proves the amalgam
nonhyperlinear does not merely produce a larger witness: it certifies that
the original shared-context group is already nonhyperlinear.

This reframes the finite packing-extension lemma as an intrinsic certificate
for the base's failure of hyperlinearity.  The finite auxiliary groups
provide a finite-dimensional proof system for that failure, while the
underlying obstruction belongs to the base.
