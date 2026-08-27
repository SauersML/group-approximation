---
rg: 2
id: sp4-metaplectic-class-pointwise-coboundary-limit
kind: claim
title: The metaplectic scalar class is not a pointwise limit of coboundaries
distinct_from:
  sp2g-z-full-c-star-algebra-has-llp: that is the still-open lifting-property hole; this decisively refutes one proposed constant-class Ioana--Spaas--Wiersma attack on it.
  deligne-central-mark-hs-collapse: that is a quantitative normalized-Hilbert--Schmidt assertion about approximate representations; the elementary closedness argument here concerns exact scalar cocycles in the pointwise topology.
---

Let `Gamma` be any discrete group.  In the product topology,

```text
B^2(Gamma,T) = delta(T^Gamma)
```

is compact, hence closed, in `Z^2(Gamma,T)`: the cochain space `T^Gamma` is
compact by Tychonoff, the coboundary map is continuous, and the cocycle
space is Hausdorff.  Therefore no nonzero class in `H^2(Gamma,T)` is a
pointwise limit of scalar coboundaries.

In particular, let `c_pi` represent the nontrivial metaplectic class of
`Gamma=Sp_4(Z)`.  There are no maps `b_n:Gamma->T` such that

```text
b_n(g)c_pi(g,h)b_n(h)b_n(gh)^(-1) -> 1                 (MC1)
```

pointwise.  Indeed `(MC1)` says that the coboundaries `delta(b_n)` converge
to `c_pi^(-1)`; closedness would make `c_pi` a coboundary.

This refutes the constant-metaplectic-class version of the
Ioana--Spaas--Wiersma Theorem A attack.  Their successful
`Z^2 rtimes SL_2(Z)` construction necessarily uses distinct nonzero
cohomology classes tending to zero, not representatives of one fixed
class.  Thus finite-dimensional realizability of only the trivial and
metaplectic classes in the Deligne circle cannot be combined with a change
of scalar gauge to produce the required cocycle sequence.
