---
rg: 2
id: peterson-innerness-kt-calibration-proof
kind: route
title: Calibrate Peterson Theorem 5.2 on the exact Kun--Thom compressor
target: peterson-innerness-does-not-collapse-kt-compressor
requires:
  - kt-compressor-pair-group-factor-ultrapower-has-no-leak
---

Choose `q=2`.  For the Kun--Thom actor, the central scalar group is

```text
Z(G)={lambda I : lambda in F_2^times, lambda^r=1}={1}.
```

The established self-ultrapower theorem
`kt-compressor-pair-group-factor-ultrapower-has-no-leak` therefore gives

```text
L(Gamma)' cap L(G)^omega=L(Z(G))^omega=C.                (PKP1)
```

In particular `L(Gamma)` is a factor.  It has property `(T)` because
`Gamma=EL_r(F_2[x_1,...,x_d])` has property `(T)` by the
Ershov--Jaikin-Zapirain theorem used in Kun--Thom Theorem E.

Let `B=L(G)` and set `alpha_n=Ad(u_t)` for every coordinate.  An inner
automorphism of a finite von Neumann algebra lies in the connected component
of the identity: write `u_t=exp(ih)` for a bounded self-adjoint `h` and use
the path `s |-> Ad(exp(ish))`.  Hence the constant ultrapower automorphism
`alpha=(alpha_n)^omega` meets Peterson Theorem 5.2's deformation hypothesis.
Together with `(PKP1)`, all of that theorem's hypotheses hold for the
constant property-`(T)` subfactor `L(Gamma) subset B^omega`.

The theorem concludes that a unitary of `B^omega` implements `alpha` on
`L(Gamma)`.  The constant `u_t` already does so.  On the other hand,

```text
alpha(L(Gamma))=u_t L(Gamma) u_t^*=L(t Gamma t^(-1))
               =L(Lambda).                              (PKP2)
```

This is proper in `L(Gamma)`: choose
`gamma in Gamma minus Lambda`.  The Fourier unitary `u_gamma` is orthogonal
to `L(Lambda)` in `L^2(L(Gamma))`, so it cannot belong to `L(Lambda)`.

Finally, if `u` and `v` both implement `alpha` on `M=L(Gamma)`, then
`u^*v` commutes with every element of `M`; conversely `uc` implements the
same map for every `c in U(M' cap B^omega)`.  This proves `(PIC5)` and
`(PIC6)`.  Peterson's conclusion is therefore fully realized while the
compressor range remains proper, proving the claimed no-go.

**Primary-source boundary.**  Peterson Theorem 5.2 states only that a
coordinatewise connected automorphism of the ambient ultraproduct is inner
*on* a property-`(T)` subfactor with factorial relative commutant.  It makes
no invariance or onto assertion for that subfactor.  The theorem statement
was checked against arXiv:2605.16669v1, lines 469--471 of the official HTML.
