---
rg: 2
id: binary-jacobson-mf-radical-dichotomy
kind: claim
title: The binary Jacobson elementary group is MF or has exactly its finitary kernel as MF radical
distinct_from:
  binary-jacobson-elementary-mark-is-finite-quotient-invisible: that places the finitary kernel in the finite residual; this computes the complete two-valued MF-radical alternative.
  binary-jacobson-head-retaining-homomorphisms-are-faithful: that treats one homomorphism retaining the mark; this identifies the intersection of all norm-corona kernels.
---

**ESTABLISHED.**  With

```text
E=EL_5(J),
L=GL_fin(N x {1,...,5},F_2),
Q_0=EL_5(F_2[z,z^(-1)]),
```
the symbol sequence is exact and `Q_0` is residually finite.  Therefore

```text
Rad_MF(E) <= L.                                        (JRD1)
```

Since `L` is simple,

```text
Rad_MF(E) in {1,L}.                                    (JRD2)
```

The two alternatives are exact:

* if `Rad_MF(E)=1`, then the countable group `E` is operator-MF;
* if `Rad_MF(E)=L`, every MF-target homomorphism factors through the
  residually finite symbol quotient `Q_0`.

Together with `binary-jacobson-steinberg-cover-is-elementary` and
`binary-jacobson-head-retaining-homomorphisms-are-faithful`, this says that
the Jacobson endpoint has no intermediate outcome:

```text
x_13(1-ST) is MF-visible  <=>  St_5(J)=E is operator-MF,
x_13(1-ST) is MF-invisible <=> Rad_MF(E)=L.             (JRD3)
```
