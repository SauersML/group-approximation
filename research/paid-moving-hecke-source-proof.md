---
rg: 2
id: paid-moving-hecke-source-proof
kind: route
title: Intersect the paid compression with the conjugated signed source and charge the forced head exit
target: paid-cut-has-moving-hecke-source-or-detector
requires:
  - paid-t00-reynolds-cut-is-whitehead-reducing
  - paid-t00-carrier-has-signed-hecke-reynolds-dichotomy
  - center-chain-mixed-hecke-overlap-is-common-pauli-source
  - el20-order-seven-heads-force-zero-common-hecke-reducing-cut
---

Write `C=P_zP_D`.  Every Pauli-menu word and every native `S_3` actor used
to form the frozen word `s=w u_epsilon^(-1)` preserves `P_z`.  Hence the paid
projection in `(PWR7)` is exactly `C_s=sCs^(-1)`, and `(PWR7)` gives
`(PMH1)`.

Conjugating `(PSD3)--(PSD5)` by `s` gives

```text
||(1-Q_s)C_s||_op<=b_s.                                (1)
```

If `b_s>=1/2`, this is `(PMH3)`.  Suppose `b_s<1/2`.  For every vector `y`
in the range of `C_s`, `(1)` gives

```text
||Q_sy||^2=||y||^2-||(1-Q_s)y||^2
          >=(1-b_s^2)||y||^2.                          (2)
```

Apply `(2)` columnwise to the Hilbert--Schmidt operator `C_sE`.  Since

```text
tau(EC_sE)=||C_sE||_2^2,
tau(Q_sC_sEC_sQ_s)=||Q_sC_sE||_2^2,
```

we obtain

```text
tau(X_s)>=(1-b_s^2)tau(EC_sE)
         >(3/4)tau(P_z)/7936
          =3tau(P_z)/31744.                            (3)
```

The support `R_s` of `X_s` lies below `Q_s`, and because `0<=X_s<=R_s`,
`tau(R_s)>=tau(X_s)`.  Conjugation by `s^(-1)` gives the positive cut
`R_0<=Q`.  Equations `(MCS3)--(MCS5)` give

```text
u_iQu_i^(-1)=P
```

for `u_1=B_2A_1` and `u_2=B_3A_2A_1`.  Therefore
`R_i=u_iR_0u_i^(-1)<=P` and `(1-R_i)u_iR_0=0`.  This proves
`(PMH4)--(PMH6)`.  Notice that the only analytic operation is selection of
the approximation-dependent support `R_s`; the transport through the Hecke
row itself is the literal ordinary word `u_i`.

For completeness, the zero-common-cut identity gives a quantitative finite
fence.  Retain

```text
g=t_1^2t_2,       k=t_1^(-2)t_2t_1^(-1),
[gdg^(-1),kfk^(-1)]=h,
dR_0=fR_0=R_0,    hR_0=-R_0.                           (4)
```

For a projection and a finite-dimensional unitary, the forward and backward
off-corner Hilbert--Schmidt boundary norms agree.  Word telescoping therefore
gives

```text
||(1-R_0)g^(-1)R_0||_2<=2epsilon_1+epsilon_2,
||(1-R_0)k^(-1)R_0||_2<=3epsilon_1+epsilon_2.          (5)
```

Because `d` and `f` are the identity on `R_0`, conjugating them by `g,k`
costs at most twice the corresponding quantity in `(5)`.  Telescoping the
four-factor commutator in `(4)` then yields

```text
2sqrt(tau(R_0))=||(h-1)R_0||_2
 <=2((4epsilon_1+2epsilon_2)+(6epsilon_1+2epsilon_2)). (6)
```

Dividing by two proves `(PMH7)`, and `(PMH8)` follows.  This also explains
why the construction evades, rather than contradicts, the zero-common-cut
theorem.

Finally, `u_1R_0u_1^(-1)` and `u_2R_0u_2^(-1)` lie in the common refined
range `P`.  The argument has not identified either with the prescribed
native quarter/eighth controlled target.  Replacing the next cut by a
tautological word conjugate leaves an arbitrary moving-frame coboundary, so
no unequal affine gauge conclusion follows from this one-row transport.
