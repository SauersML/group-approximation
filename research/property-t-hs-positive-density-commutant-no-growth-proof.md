---
rg: 2
id: property-t-hs-positive-density-commutant-no-growth-proof
kind: route
title: Combine word-form inclusion, conjugate spectral counts, and the property-T SOS budget
target: property-t-hs-positive-density-commutant-no-growth
requires:
  - property-t-hs-adjoint-low-spectrum-budget
  - hs-spectral-counting-under-perturbation
---

All traces and Hilbert--Schmidt norms below are normalized on the adjoint
space of dimension `d^2`.

**Word-form inclusion.** If `w_s` has length `ell_s`, telescoping the adjoint
action of its letters and applying Cauchy--Schwarz gives a constant `L`,
depending only on the fixed words, such that the Dirichlet forms satisfy

```text
C_alpha <= L A.                                                 (1)
```

This uses the evaluated word `phi(w_s)` itself and therefore needs no
multiplicativity assumption.

**Conjugate comparison.** Put `B=Ad(phi(t)) A Ad(phi(t))*`. The HNN relators
`(PCG1)`, `(RHG4)`, and averaging give

```text
||B-C_alpha||_2 <= C_0 delta.                                  (2)
```

The operators `A,B` are unitarily conjugate and have identical spectral
counts.

Choose fixed `0<a<b<c<kappa/2`. The property-T spectral budget gives

```text
tr(PA)<=C_1 delta,
tr(1_(a,c](A))<=C_2 delta^2.                                   (3)
```

Since `C_alpha>=b(I-Q)`, `(1)` and `(3)` imply

```text
tr(P(I-Q)) <= tr(P C_alpha)/b
             <= (L/b) tr(PA) <= C_3 delta.                     (4)
```

Apply `hs-spectral-counting-under-perturbation` to `C_alpha,B` with
thresholds `b<c` and use `(2)`. Because `B` has the same spectrum as `A`,

```text
tr(Q)
 <= tr(1_[0,c](B)) + C_0^2 delta^2/(c-b)^2
 =  tr(P)+tr(1_(a,c](A))+O(delta^2)
 <= tr(P)+C_4 delta^2.                                        (5)
```

Finally,

```text
tr(Q(I-P))=tr(Q)-tr(PQ)
 <= tr(Q)-tr(P)+tr(P(I-Q))
 <= C_4 delta^2+C_3 delta,
```

which is `(PCG2)` after enlarging the constant.

