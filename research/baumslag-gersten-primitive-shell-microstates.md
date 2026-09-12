---
rg: 2
id: baumslag-gersten-primitive-shell-microstates
kind: route
title: Close one Baumslag--Gersten seam with the sorted primitive-shell matcher
target: baumslag-gersten-mark-survives-opnorm-corona
requires:
  - primitive-shell-sorted-matcher-is-one-phase-torus
---

Fix `n>=2`, put

```text
q=3^n,                 L=2*3^(n-1),
omega=exp(2*pi*i/L),
```

and use the exponent basis and the unitaries `P,B,H` from
`primitive-shell-sorted-matcher-is-one-phase-torus`. Thus `P` is the cyclic
shift on `Z/LZ`, `B` is diagonal, and

```text
H P H^*=B,
||P B P^*-B^2||=|omega-1|=2*sin(pi/L).                 (BGM1)
```

Since `B` is unitarily conjugate to the `L`-cycle `P`, its spectrum is the
complete set of `L`-th roots of unity. Let `C` be reversal of the cyclic
basis,

```text
C e_j=e_(-j).
```

Then `C^* P C=P^*`. Put

```text
A=B,                    T=H C.                          (BGM2)
```

The conjugated generator is exactly

```text
T^* A T
 =C^* H^* B H C
 =C^* P C
 =P^*.                                                     (BGM3)
```

Therefore, writing `A^T=T^*AT`,

```text
||(A^T)^* A A^T-A^2||
 =||P B P^*-B^2||
 =2*sin(pi/L) -> 0.                                    (BGM4)
```

This is precisely the relator defect for

```text
BG=<a,t | (t^(-1) a t)^(-1) a (t^(-1) a t)=a^2>
```

under `a |-> A`, `t |-> T`. Since the presentation is finite, the sequence
of assignments gives a homomorphism from `BG` to the operator-norm matrix
corona.

Finally `L` is even, so `-1` occurs in the spectrum of `P`, hence also in the
spectrum of `B=A`. Thus

```text
||A-1||=2                                                   (BGM5)
```

at every stage. The corona image of `a` is not the identity, proving
`a notin Rad_MF(BG)`.

No stability theorem, Property `(T)`, Kazhdan input, or number-theoretic
primitive-root conjecture is used. The powers `q=3^n` and the required
one-step matcher are already explicit in the cited primitive-shell theorem.
