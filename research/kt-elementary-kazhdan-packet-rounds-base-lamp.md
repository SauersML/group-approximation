---
rg: 2
id: kt-elementary-kazhdan-packet-rounds-base-lamp
kind: claim
title: One explicit elementary Kazhdan packet rounds the Kun--Thom base lamp into the Gamma commutant
distinct_from:
  kt-single-root-mixed-return-has-exact-finite-countermodels: That proves the one-root packet is insufficient by exact finite countermodels; this supplies an explicit full generating packet and the positive dimension-free commutant-rounding estimate.
  kt-wreath-relative-canonical-actor-exactification: That asks to replace the approximate actor by a genuine representation; this starts after such a representation is available and performs only the relative lamp rounding.
  kazhdan-weak-ucp-stability-is-flexible-stability: That concerns stability of arbitrary almost representations; this is the elementary adjoint spectral-gap estimate inside one already genuine representation.
---

**ESTABLISHED.**  In the pinned `r=d=3` Kun--Thom pair, write

```text
Gamma=EL_3(F_q[x_1,x_2,x_3])
```

and take the finite symmetric packet

```text
K={e_ij(c): i!=j, c in F_q}
  union {e_ij(x_l),e_ij(-x_l): i!=j, 1<=l<=3}.       (KEP1)
```

This packet generates `Gamma`, hence, because `Gamma` has property `(T)`, it
has a Kazhdan constant `kappa_K>0`.  For every genuine finite-dimensional
unitary representation `pi` of `Gamma` and every projection `P`, there is a
projection `P_0 in pi(Gamma)'` such that

```text
||P-P_0||_2
 <= (sqrt(2)/kappa_K) max_(s in K)||[P,pi(s)]||_2.    (KEP2)
```

The estimate is dimension independent and preserves normalized trace up to
the same right-hand side.

It couples quantitatively to the explicit return `h=LrL^(-1)`.  Suppose a
canonical microstate has projection `P`, actor matrices `u_s,u_h`, and a
second lamp projection `Q`, and suppose a genuine actor representation `pi`
satisfies

```text
max_(s in K)||u_s-pi(s)||_2 <= epsilon,
||u_h-pi(h)||_2 <= epsilon,
max_(s in K)||[P,u_s]||_2 <= delta_K,
||Q-u_h P u_h^*||_2 <= delta_h.                       (KEP3)
```

Then `P_0` can be chosen as above and

```text
||P-P_0||_2 <= (sqrt(2)/kappa_K)(delta_K+2epsilon),
||Q-pi(h)P_0pi(h)^*||_2
 <= delta_h+2epsilon+(sqrt(2)/kappa_K)(delta_K+2epsilon). (KEP4)
```

Thus `(KEP1)` is a concrete finite stabilizer interface sufficient for the
lamp-rounding part of the KRE argument.  It does not prove actor
exactification and does not kill the remaining action of `pi(h)` on the
multiplicity algebra `pi(Gamma)'`; that is still the live unitary-HS gate.

DERIVATION
kt-elementary-kazhdan-packet-rounding-proof
