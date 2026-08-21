---
rg: 2
id: periodic-bs-clock-defeats-spectral-first-hit-checksum
kind: claim
title: Periodic Baumslag--Solitar clocks defeat marginal spectral first-hit checks
distinct_from:
  summable-power-return-detectors-miss-growing-cycles: that treats one arbitrary cyclic spectrum and summable return statistics; this gives exact finite models of the Baumslag--Solitar doubling relator and audits their first-hit layers.
  odd-root-wasserstein-target-is-vacuous: that concerns approximation of one marginal spectral measure; this exhibits two asymptotically Haar unitaries joined by an exact doubling conjugacy but separated by asymptotically maximal Hilbert--Schmidt distance.
  rooted-tree-first-hit-recursion-has-no-infinite-only-tail: that rules out a faithful rooted-tree mark supported only on one boundary ray; this rules out a noncontracting cyclic spectral version by exact periodic clock models.
---

Let

```text
BS(1,2)=<p,z | p z p^(-1)=z^2>.
```

For every odd integer `q`, put `zeta=exp(2 pi i/q)` on the basis
`(e_x)_(x in Z/qZ)` and define

```text
Z_q e_x=zeta^x e_x,
P_q e_x=e_(2^(-1)x).
```

Then

```text
P_q Z_q P_q^(-1)=Z_q^2                              (PBC1)
```

exactly.  There are primes `q_n->infinity` for which, for every fixed
nonzero integer `k`,

```text
tr(Z_(q_n)^k)->0,
tr(P_(q_n)^k)->0,                                    (PBC2)
```

while

```text
||P_(q_n)-Z_(q_n)||_2^2=2-2/q_n->2.                 (PBC3)
```

Thus both named unitaries have asymptotically Haar marginal spectral
measures, and the Baumslag--Solitar relation has zero defect, but their
joint eigenvector geometry is maximally incoherent.

The same models defeat a spectral first-hit implementation.  Conjugation
by `P_q` permutes the spectral atoms of `Z_q` periodically.  If a singleton
challenge atom lies in an orbit of length `ell`, its first `ell` first-hit
layers are one-dimensional and hence each has normalized trace `1/q`.
Every unitary comparison localized on one such layer has squared normalized
Hilbert--Schmidt cost at most `4/q`, while the doubling relator remains
exact on every layer.  The remaining atoms are periodic persistent orbits,
not an absorbing infinite tail.

Consequently a noncontracting cyclic host does not realize the square-function
compiler merely from:

1. the local Baumslag--Solitar conjugacy defects;
2. individual power moments or spectral measures of the clock and
   conjugator; and
3. first-hit projections for the induced finite spectral permutation.

A viable cyclic checksum must control genuinely joint eigenbasis holonomy
or identify the same operator occurrence around the whole cycle.  Marginal
Haar behavior plus exact local doubling supplies no such control.

