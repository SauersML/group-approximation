---
rg: 2
id: z-haar-algebraic-factors-have-lebesgue-plus-torsion-spectrum
kind: claim
title: Factors of Haar algebraic Z-actions have only Lebesgue and torsion point spectrum
distinct_from:
  haar-algebraic-actions-have-permutation-koopman-spectrum: that gives the general permutation-representation obstruction and notes the irrational-eigenvalue test; this computes the complete spectral-type restriction for one acting automorphism.
  algebraic-compact-action-envelope-for-non-ce-relation: that permits a non-base-equivariant inclusion of crossed products; this only rules out measurable action factors and Gaussian compactification attempts.
---

Let `T` be a continuous automorphism of a compact second-countable abelian
group `K`, preserving Haar measure.  If a probability-preserving
`Z`-action `(X,mu,S)` is a measurable factor of `(K,Haar,T)`, then every
spectral measure of its Koopman operator is absolutely continuous with
respect to

```text
m_T + sum_{zeta in Tor(T)} c_zeta delta_zeta,             (ZAS1)
```

where `m_T` is Haar measure on the circle, `Tor(T)` is the countable set of
roots of unity, and the `c_zeta` are arbitrary fixed positive summable
weights.  In particular, such a factor has no singular-continuous Koopman
spectrum and has no irrational point eigenvalue.

Consequently a Gaussian action whose first chaos has a nonzero
singular-continuous spectral measure cannot be a factor of any Haar
compact-abelian algebraic `Z`-action.  Passing from a Gaussian probability
space to a compact model therefore does not evade the Haar algebraic
obstruction.
