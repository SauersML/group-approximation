---
rg: 2
id: cuspidal-redistribution-refutes-x-central-root-alignment
kind: route
title: Align the split Weyl involutions in the cuspidal redistribution family and apply the modular Selberg gap
target: x-central-root-alignment-fails-inside-one-exact-stratum
requires:
  - cuspidal-redistribution-refutes-regular-core-orbit-basin
---

Let `p=1 mod 4`, put `Q_p=PSL_2(F_p)`, and use the regular representation
`rho_p` and the cuspidally redistributed representation `eta_p` from
`cuspidal-redistribution-refutes-regular-core-orbit-basin`.  Write

```text
x=w=[0 -1;1 0],          t=u(1),          r=h(2).       (XCP1)
```

The redistribution changes only the multiplicities of the degree-`p-1`
cuspidal representations.  Their character values agree on every split
semisimple element.  Since `p=1 mod 4`, `-1` is a square and the Weyl
involution `x` is split semisimple.  Consequently

```text
chi_(eta_p)(x)=chi_(rho_p)(x)=0.                       (XCP2)
```

Both matrices at `x` are involutions, so equality of their traces and
dimensions gives a unitary `y_p` for which

```text
y_p eta_p(x)y_p^*=rho_p(x)=:X_p.                      (XCP3)
```

Define

```text
(R_(0,p),T_(0,p))=(rho_p(r),rho_p(t)),
(R_(1,p),T_(1,p))=(y_p eta_p(r)y_p^*,y_p eta_p(t)y_p^*).
                                                               (XCP4)
```

These are exact endpoints under the common involution `X_p`.  The
redistribution construction gives
`Res_<r,t>(eta_p)~=Res_<r,t>(rho_p)`, hence the two roots in `(XCP4)` have
the same spectral multiplicities.  Taking `K_p=ord_p(4)` makes the order-`p`
unipotent satisfy `T_(i,p)^(4^(K_p)-1)=1`, so these are exact cores at the
required dyadic one-power level.

It remains to prove the uniform separation.  On
`Hom(H_(rho_p),H_(eta_p))`, after the conjugation by `y_p`, consider

```text
beta_p(g)Z=(y_p eta_p(g)y_p^*) Z rho_p(g)^*.           (XCP5)
```

For a unitary `z` commuting with `X_p`, its displacement under `x` is zero,
while

```text
||beta_p(t)z-z||_2
 =||T_(1,p)-zT_(0,p)z^*||_2.                          (XCP6)
```

The fixed generating pair `(x,t)` is the standard modular pair and its
reductions generate `Q_p`.  Selberg property `(tau)` therefore supplies a
constant `kappa>0`, independent of `p`, such that

```text
||beta_p(t)z-z||_2
 >= kappa dist_2(z,Hom_(Q_p)(rho_p,y_p eta_p y_p^*)).  (XCP7)
```

The representation-multiplicity computation in the cuspidal
redistribution proof applies to every unitary, independently of `(XCP3)`.
With `m_p=(p-1)/4` and `d_0=p-1`, it gives

```text
dist_2(z,Hom_(Q_p)(rho_p,y_p eta_p y_p^*))^2
 >= ((m_p-1)d_0^2)/|Q_p| -> 1/2.                     (XCP8)
```

Combining `(XCP6)--(XCP8)` proves `(XCA2)`, for example with any fixed
`c<kappa/sqrt(2)` after discarding finitely many primes.  In particular, an
exact `X_p`-central root alignment would itself intertwine the two
representations on the generators `(x,t)` and is impossible even before
the quantitative gap is invoked.
