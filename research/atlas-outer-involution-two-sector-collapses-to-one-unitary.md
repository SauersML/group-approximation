---
rg: 2
id: atlas-outer-involution-two-sector-collapses-to-one-unitary
kind: claim
title: The coherent two-sector A8 outer-label ansatz collapses to one coefficient unitary
invalidates:
  - atlas-outer-involution-two-sector-model
distinct_from:
  atlas-a4-19243-classical-collapse: that excludes the two scalar inner and outer automorphism alignments by literal packet and collision words; this treats an operator-valued coherent interpolation between those label sectors at arbitrary growing multiplicity.
  atlas-full-coefficient-automorphism-twists-are-gauge: that applies one automorphism simultaneously to all coefficients of an arbitrary relative unitary; this analyzes a position-dependent relative unitary controlled by the two spectral projections of the genuine outer A8 label involution.
  atlas-equal-block-flattening-is-commutant-gauge: that shows equal block norms are gauge for every relative unitary; this gives the exact gauge-normal form and a uniform defect wall for one structured outer-label ansatz.
---

**ESTABLISHED SCOPED NO-GO.**  Let `sigma in Aut(A8)` be an outer
involution, and let the real permutation unitary `W` on `l2(A8)` satisfy

```text
W lambda(g) W^*=lambda(sigma(g)),       W=W^*=W^(-1). (OIT1)
```

Put `P_plus=(I+W)/2`, `P_minus=(I-W)/2`.  For arbitrary
`V_plus,V_minus in U(r)`, define

```text
U=P_plus tensor V_plus + P_minus tensor V_minus.      (OIT2)
```

Then `U` is unitary, but its complete two-chart word data depend, up to a
legal commutant gauge, on only the single unitary

```text
Z=V_plus V_minus^*.                                  (OIT3)
```

Indeed right multiplication by `I tensor V_minus^*`, which commutes with
the untransported regular second chart, does not change that transported
chart and gives

```text
U'=U(I tensor V_minus^*)
  =P_plus tensor Z + P_minus tensor I.                (OIT4)
```

Every `A8 by A8` block coefficient of `U'` belongs to the one-unitary
algebra `C*(Z)`, hence is contained in a finite-dimensional commutative
star algebra.  Therefore the internal-complexity mass in
`leavitt-regular-atlas-block-monomial-gap` has `w_1(U')=1`, and its fixed
constant `e_1>0` gives

```text
F_r(U)^2=F_r(U')^2 >= e_1.                            (OIT5)
```

No sequence of the form `(OIT2)` can establish the regular Atlas
hyperlinearity criterion.  This remains true even when the **raw** pair
`V_plus,V_minus` generates `M_r(C)` and has macroscopic commutators: that
raw fullness is destroyed by a word-invisible right commutant gauge, so it
is not authenticated coefficient complexity.

The result pinpoints the first surviving outer-label architecture.  A
coherent model needs at least three effective label modes with two relative
coefficient unitaries generating growing noncommutative algebras, or must
leave spectral control by the outer involution entirely.  It does not claim
that either larger architecture is feasible.

DERIVATION
atlas-outer-involution-two-sector-collapse-proof
