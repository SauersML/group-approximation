---
rg: 2
id: tensor-power-common-return-no-go-proof
kind: route
title: Decompose the tensor kernel by its bad-factor subsets
target: tensor-power-deficiency-amplification-loses-common-return
requires: []
---

Split the source as `ker(A) direct_sum ker(A)^perp`.  Tensor distributivity
decomposes the `k`-fold source into summands indexed by subsets of bad
factors.  Every nonempty subset lies in the tensor kernel, giving density
`1-(1-beta)^k`.  A return unitary which is identity on the bad factor and a
generic scalar on its complement acts on each subset summand by a different
nontrivial scalar; only the all-bad summand is fixed.  Its density is
`beta^k`.  Generic small perturbations of asymptotically Haar complement
spectra preserve this conclusion while making every fixed nonzero word
moment vanish.
