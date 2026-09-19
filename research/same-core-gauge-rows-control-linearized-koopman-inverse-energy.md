---
rg: 2
id: same-core-gauge-rows-control-linearized-koopman-inverse-energy
kind: claim
title: Over every exact BS core, the Iwahori Fox rows uniformly control linearized inverse-Koopman gauge energy
artifacts:
  - experiments/iwahori_cycle_gauge_gap.py
  - research/artifacts/iwahori-cycle-gauge-gap-audit-2026-08-23.md
distinct_from:
  iwahori-cubics-control-aggregate-weighted-bs-orbit-energy: that is a global nonlinear finite-defect assertion; this proves the complete weighted estimate for every tangent gauge at every unitary over an exact BS core, including nonextendable outliers, but does not integrate the tangent estimate in normalized Hilbert--Schmidt norm.
  same-core-involution-cubic-gauge-coercivity: that is a global nonlinear distance estimate relative to an exact extending endpoint; this needs no exact endpoint or exact Iwahori row and instead controls the full Fox differential at an arbitrary unitary over the core.
  koopman-weighted-energy-is-linearized-gauge-distance: that identifies inverse energy with minimum gauge norm but supplies no row coercivity; this supplies the row coercivity in the authenticated same-core basin.
---

Let `(R,T)` be any exact finite-dimensional square-free `BS(1,4)` core and
let `X` be an arbitrary unitary:

```text
RTR^(-1)=T^4.                                          (SCK1)
```

Put `Z={T}'`, let `psi=Ad(R^(-1))` on `L^2(Z)`, and for `A in Z` define

```text
D A=A-psi(A),
L_2 A=A+Ad(X)(A),
L_3 A=A+Ad(XT)(A)+Ad((XT)^2)(A).                      (SCK2)
```

Thus `L_2` and `L_3` are the left-trivialized differentials of `X^2` and
`(XT)^3` under the same-core gauge perturbation
`X_epsilon=exp(epsilon A)X`, while `D` is the differential of the
Weyl-conjugacy residual.  If `P_t` are the dyadic spectral bands of `psi`,
then

```text
sum_t t^(-2)||P_t D A||_2^2
 <= 2(||L_2 A||_2^2+||L_3 A||_2^2).                  (SCK3)
```

Equivalently, after quotienting the domain by `ker(D)`, the generalized
smallest singular value of the row column `(L_2,L_3)` relative to exact
inverse-Koopman energy is at least `1/sqrt(2)`.  Adding the inversion and
second-cubic rows can only increase this value.

No Iwahori relation involving `X` is assumed in `(SCK3)`: `X^2`, `(XT)^3`,
and the second cubic may all have nonzero baseline defect.  The constant is
independent of matrix dimension, fourth-power cycle length, packet
multiplicity, and return monodromy.  It also includes
heterogeneous orthogonal sums and the off-diagonal commutant intertwiners
between their coincident `T`-eigenvalues: no packetwise decomposition is
used in the proof.

On a scalar fourth-power cycle of length `m`, `(SCK3)` is exactly

```text
sum_(j != 0) |widehat(D A)(j)|^2
                  /|1-exp(2 pi i j/m)|^2
 <=2(||L_2 A||_2^2+||L_3 A||_2^2),                  (SCK4)
```

The displayed left side is the stronger full spectral inverse; restricting
to the low dyadic bands only decreases it, and replacing exact spectral
weights by band endpoints changes it by at most the usual factor four.
Hence long cycles and simultaneous recycling over many low modes do **not**
cause a generalized singular-value loss, even at an outlier extender.

## Scope of the reduction

This still does not establish
`iwahori-cubics-control-aggregate-weighted-bs-orbit-energy`.  The estimate is
for the Fox differential, whereas `(IAG1)` is a global normalized-HS error
bound.  Uniform pointwise injectivity of the differential cannot simply be
integrated: operator-norm Taylor control is unavailable, rank-concentrated
paths can cross different exact endpoint fibers, and strict repair is known
to fail on compressed even-Weil blocks.  The remaining content is therefore
a nonlinear metric-regularity/flexible endpoint-selection theorem, not a
finite-cycle singular-value estimate.  The compressed even-Weil outliers are
consistent with this boundary: their inversion residual is zero, while
their cubic defect records the missing boundary dimension.
