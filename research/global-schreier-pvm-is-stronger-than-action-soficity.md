---
rg: 2
id: global-schreier-pvm-is-stronger-than-action-soficity
kind: claim
title: Global Schreier-PVM extraction is strictly stronger than soficity of the action
distinct_from:
  infinite-schreier-pvm-transport-kills-finite-mark: that proves the Poincare inequality after a finite-support PVM is supplied; this identifies the approximation notion encoded by that PVM and compares it with action soficity and raw Bernoulli covariance.
  arithmetic-global-pvm-does-not-bypass-coset-action-gate: that describes finite weighted Bernoulli models after a global lamp PVM is granted; this shows that a globally site-labelled PVM over the nonamenable Schreier set is a stronger and already impossible object.
  coordinate-action-not-sofic: that proves nonsoficity for the separate Kun--Thom pair and stresses that non-Cartan hyperlinear models remain possible; this is the arithmetic `A/C` extraction audit and does not assume its action is nonsofic.
---

Let a finitely generated group `A` act transitively on a countable set `X`
whose symmetric Schreier operator has bottom gap `gamma>0`. Call a sequence
of matrix data a **global Schreier-PVM model of mass `mu`** if it consists of
finite-support orthogonal projection families `(E_x^(n))_(x in X)` and actor
unitaries `U_s^(n)` such that

```text
liminf_n sum_x tr(E_x^(n))>=mu,
(1/|S|)sum_s sum_x
 ||U_s^(n)E_x^(n)(U_s^(n))^*-E_(sx)^(n)||_2^2 ->0.     (GSP1)
```

Then necessarily `mu=0`. Quantitatively, at every matrix level,

```text
(1/|S|)sum_s sum_x
 ||U_sE_xU_s^*-E_(sx)||_2^2
 >=2 gamma sum_x tr(E_x).                              (GSP2)
```

For the arithmetic pair

```text
C=SL_3(Z) < A=SL_3(Z[1/2]),             X=A/C,         (GSP3)
```

property `(T)` of `A` and infinite index of `C` give such a positive bottom
gap. Hence any decoder from canonical HNN microstates to `(GSP1)` would
already prove the desired microstates impossible, with the explicit modulus
`(GSP2)`.

This extraction is **stronger than soficity of the set action**, not
equivalent to it. A sofic action supplies finite local orbit charts on each
prescribed finite subset of `X`; it does not label almost all points of one
finite model by a single global finite-support map into `X`. Indeed the
regular action of any infinite nonamenable sofic group is a sofic action and
has a positive Schreier gap, so `(GSP1)` is impossible for it by `(GSP2)`.
Thus even a proof that the arithmetic action `A action A/C` is sofic would
not construct the PVM required here.

Conversely, nonsoficity of the action is weaker than the desired HNN
nonhyperlinearity conclusion. It excludes permutation/Cartan models, but a
hyperlinear model may embed the lamp algebra non-Cartanly. This is exactly
the surviving possibility in the Kun--Thom comparison. Therefore deciding
soficity of `A action A/C` does not settle the arithmetic hyperlinear route
in either direction.

## Exact Bernoulli firewall

The raw Bernoulli lamp relations do not contain `(GSP1)`. In the exact
crossed product

```text
L^infinity({0,1}^X) rtimes A,                           (GSP4)
```

the balanced coordinate projections `P_x` satisfy exact actor covariance,
but

```text
tau(P_x)=1/2,              tau(P_xP_y)=1/4   (x!=y).   (GSP5)
```

They are not a PVM. More strongly, there is no nonzero exactly covariant
countable PVM `(E_x)` in the Bernoulli algebra whose sum is an invariant
projection `R`: if `tau(R)>0`, then

```text
nu(x)=tau(E_x)/tau(R)                                  (GSP6)
```

is an `A`-invariant probability measure on `X`, contradicting the Schreier
gap (equivalently, non-coamenability of `C`).

The same argument is an exact ultraproduct firewall. In any matrix tracial
ultraproduct carrying an exact copy of the actor, every exactly covariant,
countably complete `X`-indexed PVM has zero total projection. Growing finite
supports need not converge coordinatewise to a countably complete PVM--mass
could escape to infinity--which is precisely why one should use `(GSP2)`
before taking the ultraproduct. That inequality excludes positive escaping
mass as well. Thus a hypothetical hyperlinear Bernoulli/HNN model must keep
its lamp image non-atomic or non-Cartan with respect to the site labels.

Thus the normalized-HS Poincare estimate is already complete and
window-independent once a global orthogonal label algebra exists. The
entire missing theorem is the nonlinear Cartan/PVM extraction from raw
overlapping Bernoulli lamps. It is strictly stronger than action soficity
and cannot be obtained from the raw covariance square function alone.
