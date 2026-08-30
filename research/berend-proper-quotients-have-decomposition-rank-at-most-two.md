---
rg: 2
id: berend-proper-quotients-have-decomposition-rank-at-most-two
kind: claim
title: Every proper quotient of the Berend crossed product has decomposition rank at most two
distinct_from:
  berend-torus-actions-give-strongly-qd-polycyclic-groups: that proves quasidiagonality of every representation and only records subhomogeneity of nonfaithful images; this computes a uniform decomposition-rank bound for all proper quotients.
  stw99-lxxxvi-berend-groups-decomposition-rank: that asks whether the full Berend crossed product has infinite decomposition rank; this proves that no proper quotient can witness such infinitude.
artifacts:
  - research/artifacts/stw99-lxxxvi-berend-frontier-2026-08-30.md
---

Let `Gamma = Z^2` act on `T^3` by the Berend unit action and put
`A = C(T^3) ⋊ Gamma`.  For every nonzero ideal `I` of `A`,

`dr(A/I) <= 2`.                                                `(BPQ1)`

More precisely, `A/I` is a quotient of a finite direct sum

`direct_sum_j M_{|O_j|}(C(T^2))`,                              `(BPQ2)`

where the `O_j` are finite `Gamma`-orbits.  Thus a proof that
`dr(A) = infinity` cannot descend decomposition rank to a proper quotient:
all proper quotients already have a uniform two-dimensional bound.
