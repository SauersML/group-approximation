---
rg: 2
id: same-core-gauge-rows-control-linearized-koopman-inverse-energy
kind: claim
title: Same-core Iwahori rows uniformly control the linearized inverse-Koopman gauge energy
artifacts:
  - experiments/iwahori_cycle_gauge_gap.py
  - research/artifacts/iwahori-cycle-gauge-gap-audit-2026-08-23.md
distinct_from:
  iwahori-cubics-control-aggregate-weighted-bs-orbit-energy: that is a global nonlinear assertion before an exact extending endpoint over the repaired BS core has been authenticated; this proves the complete weighted estimate for every tangent gauge after such a same-core endpoint is fixed.
  same-core-involution-cubic-gauge-coercivity: that is a global nonlinear distance estimate for a unitary gauge; this identifies its differential with the fourth-power inverse-Koopman energy, takes the fixed-algebra quotient, and proves the generalized singular-value floor including heterogeneous commutant blocks.
  koopman-weighted-energy-is-linearized-gauge-distance: that identifies inverse energy with minimum gauge norm but supplies no row coercivity; this supplies the row coercivity in the authenticated same-core basin.
---

Let `(X_0,R,T)` be an exact finite-dimensional endpoint for the square-free
Iwahori presentation:

```text
X_0^2=1,        (X_0R)^2=1,        (X_0T)^3=1,
RTR^(-1)=T^4,   (X_0T^2R)^3=1.                         (SCK1)
```

Put `Z={T}'`, let `psi=Ad(R^(-1))` on `L^2(Z)`, and for `A in Z` define

```text
D A=A-psi(A),
L_2 A=A+Ad(X_0)(A),
L_3 A=A+Ad(X_0T)(A)+Ad((X_0T)^2)(A).                  (SCK2)
```

Thus `L_2` and `L_3` are the left-trivialized differentials of `X^2` and
`(XT)^3` under the same-core gauge perturbation
`X_epsilon=exp(epsilon A)X_0`, while `D` is the differential of the
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

The constant in `(SCK3)` is independent of matrix dimension, fourth-power
cycle length, packet multiplicity, and return monodromy.  It also includes
heterogeneous orthogonal sums and the off-diagonal commutant intertwiners
between their coincident `T`-eigenvalues: no packetwise decomposition is
used in the proof.

On a scalar fourth-power cycle of length `m`, `(SCK3)` is exactly

```text
sum_(j != 0) |widehat(D A)(j)|^2
                  /|1-exp(2 pi i j/m)|^2
 <=2(||L_2 A||_2^2+||L_3 A||_2^2),                  (SCK4)
```

up to the factor-four convention in dyadic banding.  Hence long cycles and
simultaneous recycling over many low modes do **not** cause a singular-value
loss once an exact extender over the same core is available.

## Scope of the reduction

This does not establish
`iwahori-cubics-control-aggregate-weighted-bs-orbit-energy`.  Before a
same-core exact extender `X_0` is selected, the identity behind `(SCK3)` is
unavailable: in particular `Ad(X_0T)` need not have order three.  The
remaining global content is therefore endpoint/basin authentication (or an
equivalent flexible outlier repair), not a Fourier estimate on authenticated
cycles.  The compressed even-Weil outliers are consistent with this
boundary: their inversion residual is already zero, while their small cubic
defect records the missing boundary dimension.

