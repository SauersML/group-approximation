---
rg: 2
id: finite-cocycle-power-return-countermodel
kind: route
title: Specialize the common SELECT gauge to the nontrivial C2 character
target: finite-cocycle-select-has-an-exact-power-return
requires: []
---

Take `K=C_2={1,s}` and represent the payload involution `w_s` by `-I` on a
nonzero multiplicity space.  On the one-negative-character orbit of the
lamp group, use the ordered coordinate basis `(e_1,e_s)`.  The natural
packet representation has

```text
L_s=[[0,I],[I,0]],
C=diag(I,-I).
```

The operator `C` commutes with every lamp.  Moreover, at either coordinate,

```text
C_x C_(s^(-1)x)^(-1)=-I=w_s,
```

so it satisfies exactly the covariance relations `(FCS1)` of
`finite-cocycle-select-forces-one-common-lcu-gauge`.  This is its classified
form `C_x=w_xA` with the permitted common gauge `A=I`.

Let

```text
eta=2^(-1/2)(e_1+e_s),
q=|eta><eta| tensor I.
```

Direct multiplication gives

```text
qCq=<eta,C eta>q=0,
C^2=I,
qC^2q=q.
```

Hence `(FPR1)--(FPR2)` hold exactly.  Tensoring the representation by an
arbitrary multiplicity space preserves the corner-normalized defect, so no
dimension-independent robust exactification statement can turn these
relations into coherent second powers.

For the general finite-group dichotomy, the homomorphism law gives

```text
P^2=|K|^(-2)sum_(g,h)w_(gh)=P,
P^*=|K|^(-1)sum_g w_(g^(-1))=P.
```

So `P` is a projection and `||PA||=||P||` is zero or one.  If `P=0`, choose
the permitted gauge `A=I`.  For the exponent `r` of `K`, the classified
controller `C=diag(w_x)` has `C^r=I`, proving `(FPR2K)`.

For the general statement, take a nontrivial finite character `chi` and set
`w_x=chi(x)I`, `A=I`.  Character orthogonality gives `qCq=0`, while
`chi(x)^r=1` gives `C^r=I` and therefore `qC^r q=q`.
