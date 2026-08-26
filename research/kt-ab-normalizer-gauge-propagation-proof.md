---
rg: 2
id: kt-ab-normalizer-gauge-propagation-proof
kind: route
title: Rewrite the returned B-fold through the cyclic normalizer word
target: kt-ab-normalizer-row-forces-wall-gauge-propagation
requires:
  - kt-two-positive-compressors-generate-full-obstruction
  - kt-nested-compressor-flat-tower-has-uniform-wall
---

The identity `c_i=a_i b_i^*` gives

```text
b_i^*=a_i^*c_i,                 b_i=c_i^*a_i.
```

Therefore

```text
h_i=a_i^* c_i x c_i^* a_i.                              (KPP1)
```

Insert the common target `y` from `(KGP2)`.  Unitary invariance and the
triangle inequality give

```text
||h_0-h_1||_2
 <=||c_0xc_0^*-y||_2
   +||a_0^*ya_0-a_1^*ya_1||_2
   +||c_1xc_1^*-y||_2.                                  (KPP2)
```

For any unitary `y`,

```text
||a_0^*ya_0-a_1^*ya_1||_2<=2||a_0-a_1||_2,             (KPP3)
```

which proves `(KGP5)`.  The normalizer-row errors in `(KGP4)` are exactly
the defects of the fixed full-actor relations

```text
(A B^(-1)) gamma (B A^(-1))=alpha_C(gamma).             (KPP4)
```

Hence they vanish in any asymptotic model of the full actor.  Combining
`(KGP5)` with the flat-wall norm lower bound
`||h_0-h_1||_2>=sqrt(2)-o(1)` proves `(KGP6)` and the shared-`A` defect
alternative.

For context, if `rho_0,rho_1` are exact ultraproduct representations
agreeing on `Gamma`, their relative actor unitaries

```text
z_g=rho_1(g)^*rho_0(g)
```

lie in the appropriate relative commutants and obey the noncommutative
cocycle identity

```text
z_(gk)=rho_1(k)^* z_g rho_1(k) z_k.                     (KPP5)
```

Equation `(KGP5)` is the first quantitative conservation law imposed on this
cocycle by `C=AB^(-1)`.  It forces propagation but does not force the cocycle
to vanish; claiming the latter would be precisely the still-open
multiplicity-sensitive upgrade excluded by the profinite stationary-flow
and A,B-only regular-wreath countermodels.
