---
rg: 2
id: infinite-permutation-augmentation-pair-fails-relative-t
kind: claim
title: Every infinite permutation augmentation lamp pair fails relative property T
invalidates:
  - relative-kazhdan-correction-closes-word-energy
distinct_from:
  lamp-cartan-inclusion-is-not-rigid: that uses the full direct-sum lamp module; relative property T does not formally pass from that larger pair to the index-two augmentation subgroup, so this proves the missing augmentation statement by pushing the Bernoulli measures to its dual quotient.
  relative-kazhdan-bimodule-requires-whole-module-covariance: that computes why a proposed Hilbert--Schmidt action does not descend to the semidirect product; this proves that the actual augmentation semidirect pair has no relative Kazhdan projection even after descent.
  aperiodic-module-forbids-prescribed-hs-bimodule-extension: that is a finite-dimensional spectral-support obstruction to one prescribed extension; this constructs genuine infinite-dimensional representations of the augmentation semidirect product with almost invariant vectors and no module-fixed vectors.
---

**ESTABLISHED.**  Let a countable group `A` act by permutations on a
countably infinite set `X`, and put

```text
L=direct_sum_X C_2,
M=ker(sum:L->C_2),
Gamma=M rtimes A.                                         (APRT1)
```

Then the pair `(Gamma,M)` does not have relative property `(T)`.  More
precisely, there are unitary representations `pi_q` of `Gamma`, for
`q->0`, with unit vectors `xi_q` such that

```text
pi_q(a)xi_q=xi_q                         for every a in A,
||pi_q(m)xi_q-xi_q||_2 -> 0              for every m in M, (APRT2)
```

but `pi_q` has no nonzero `M`-invariant vector for any `q`.

Consequently the augmentation hosts in the infinite-character actor program
cannot instantiate the relative-property-`(T)` hypothesis of
`relative-kazhdan-bimodule-upgrades-finite-covariance`.  In particular, even
an exact correction of the proposed covariance bimodule would not make a
relative Kazhdan projection available for the actual semidirect pair.  The
actor's property `(T)` and the counting-measure gaps on infinite character
orbits do not change this conclusion: invariant diffuse Bernoulli measures
on the dual augmentation module supply the almost-invariant vectors.

