---
rg: 2
id: mod-p-regular-packet-matrix-range-proof
kind: route
title: Put the mod-p regular lattice packet in the matrix range and use denominator transport to bound every arithmetic extension
target: p-congruence-packet-is-ucp-exact-but-actor-nonextendable
requires:
  - one-britton-moment-forces-uniform-actor-noncorrectability
---

The homomorphism

```text
Lambda -> SL_3(F_p) -> U(r)
```

and its twofold amplification define a unital star homomorphism
`C^*(Lambda)->M_(2r)` sending the canonical generator `u_g` to `X_g`.
Hence `(PCE3)` holds.  Both `T` and `H` act only on the multiplicity factor,
so they commute with every `X_g`, proving `(PCE4)`.  Direct multiplication
gives

```text
[T_0,H_0]=T_0 H_0 T_0 H_0^*= [[0,1],[-1,0]],
```

whose normalized trace is zero; this proves `(PCE5)`.

It remains to prove the explicit outlier bound without invoking
superrigidity or the congruence subgroup property.  In the regular
representation, the nonidentity element `s mod p` has trace zero and order
`p`; therefore

```text
X_s^p=I,                 ||X_s-I||_2=sqrt(2).           (PCE8)
```

Fix an exact `rho:Gamma->U(d)` and set

```text
a=||rho(s)-X_s||_2,      b=||rho(h)-H||_2.
```

The arithmetic root relation and word telescoping give

```text
rho(h)rho(s)rho(h)^*=rho(s)^p,
||rho(s)^p-X_s^p||_2<=p a.                              (PCE9)
```

Since `H` commutes with `X_s`, unitary Lipschitz estimates and `(PCE8)`
now give

```text
sqrt(2)
 =||H X_s H^*-I||_2
 <=||H X_s H^*-rho(h)rho(s)rho(h)^*||_2
    +||rho(s)^p-X_s^p||_2
 <=2b+(p+1)a.                                           (PCE10)
```

Consequently `max(a,b)>=sqrt(2)/(p+3)`.  Since `s in S`, taking the
infimum over all exact `rho` proves the first direct bound in `(PCE6)`.
Finally `(PCE4)--(PCE5)` make `delta_C=delta_B=0`, so `(BNC3)` in
`one-britton-moment-forces-uniform-actor-noncorrectability` gives the
simultaneous lower bound `zeta>=c_*`.  This proves `(PCE6)` and places the
packet in the exact quantified stratum used by FDG.
