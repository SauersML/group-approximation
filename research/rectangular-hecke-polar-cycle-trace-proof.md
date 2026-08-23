---
rg: 2
id: rectangular-hecke-polar-cycle-trace-proof
kind: route
title: Polarize each bounded-below arrow, telescope carrier traces, and test algebraicity on the circle
target: rectangular-hecke-polar-cycle-has-no-strict-trace-gain
requires:
  - first-cycle-signed-hecke-chord
  - fixed-rank-index-authenticator-has-gap-or-functoriality
---

The lower bound in `(RHP1)` says that `|T_i|` has support exactly `p_i`.
The polar decomposition therefore gives `v_i^*v_i=p_i`; because
`T_i=p_(i+1)T_i p_i`, its range projection is dominated by `p_(i+1)`.
Traciality gives

```text
tau(p_i)=tau(v_i^*v_i)=tau(v_i v_i^*)<=tau(p_(i+1)).   (RHT1)
```

Chaining `(RHT1)` around the cycle begins and ends with `tau(p_0)`, so every
inequality is equality.  Since `p_(i+1)-v_i v_i^*` is a positive projection
of trace zero, it vanishes.  This proves `(RHP4)`.  If one instead declares
the next source to be only `v_i v_i^*`, the same computation applies to the
reduced carriers and the unused complement never enters the composite.

For the algebraic assertion, identify

```text
L(Z)=L^infinity(T),       u(z)=z.
```

The function `2+z` has modulus at least one, so its polar part `(RHP5)` is a
unitary in `L(Z)`.  If it were a Laurent polynomial, then every
unit-modulus Laurent polynomial on the circle being a scalar monomial would
give `polar(T)=c z^n`.  Squaring and cancelling absolute values would imply

```text
(2+z)/(2+z^(-1))=c^2 z^(2n).                           (RHT2)
```

The left side is `z(2+z)/(2z+1)` and has a zero at `-2` and a pole at
`-1/2`; it is not a monomial.  This contradiction proves that the polar
unitary lies outside `C[Z]`.
