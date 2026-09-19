---
rg: 2
id: minimal-stinespring-boundary-proof
kind: route
title: Prove the finite regular coefficient vector is cyclic
target: canonical-boundary-enemy-is-minimal-stinespring
requires:
  - canonical-hnn-flat-boundary-enemy
---

The vector used in `flat-singular-canonical-polar-proof` has the form

```text
xi=sqrt(a) eta+sqrt(1-a) zeta,
zeta=(delta_e-|Q|^(-1/2)eta)/sqrt(1-|Q|^(-1)),           (MSB1)
```

where `eta` is the invariant unit vector and `0<a<1`.  Thus
`xi=c delta_e+d eta` with `c nonzero`, and its invariant component is also
nonzero.  Differences of its regular translates are

```text
lambda_Q(g)xi-lambda_Q(h)xi=c(delta_g-delta_h).          (MSB2)
```

They span `eta^perp`, while the average of the translates is the nonzero
invariant component.  Therefore

```text
span{lambda_Q(g)xi:g in Q}=ell2(Q).                      (MSB3)
```

For every `a in A`, since `lambda_G(a)` is onto,

```text
pi(a)V L2(G)=L2(G) tensor C lambda_Q(q(a))xi.            (MSB4)
```

The quotient map is onto `Q`; `(MSB3)` and `(MSB4)` show

```text
closure span pi(C*(A))V L2(G)=L2(G) tensor ell2(Q).      (MSB5)
```

This is precisely Stinespring minimality.  Formula `(CMS3)` is the usual
defect identity

```text
V*pi(s)^*(1-VV*)pi(s)V=(1-|f(s)|^2)I.                   (MSB6)
```

and minimal Stinespring dilations are unitarily equivalent by a unitary
fixing the embedded input space.  Hence the leakage cannot be removed by
passing to a minimal or canonical representative.
