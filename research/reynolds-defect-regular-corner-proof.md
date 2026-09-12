---
rg: 2
id: reynolds-defect-regular-corner-proof
kind: route
title: Spectrally cut the averaged relator defect and polar-correct its compression
target: reynolds-defect-cut-gives-regular-relator-corner
requires: []
---

Conjugation by `rho(g)` permutes the summands in `(RDC1)`, so `Delta_H`
commutes with `rho(H)` and hence so does `q`.  Also

```text
tr(Delta_H)=||Y-I||_2^2=d^2.
```

Markov's spectral inequality gives `(RDC2)`.

Because the identity summand occurs in `(RDC1)`,

```text
(Y-I)^*(Y-I) <= |H| Delta_H.
```

On the range of `q`, `q Delta_H q<=s q`; therefore

```text
||(Y-I)q||_(2,q)^2<=|H|s.                              (RDC8)
```

Since `(1-q)q=0`,

```text
tr_q(q-C^*C)
 =||(1-q)Yq||_(2,q)^2
 <=||(Y-I)q||_(2,q)^2<=|H|s.                          (RDC9)
```

In the finite matrix corner extend the polar part of `C` to a unitary `B`.
Singular-value calculus gives

```text
||C-B||_(2,q)^2
 =tr_q((q-|C|)^2)
 <=tr_q(q-|C|^2)=tr_q(q-C^*C).                        (RDC10)
```

Moreover `C-q=q(Y-I)q`, so `(RDC8)--(RDC10)` prove `(RDC3)`.  From
`K=(q+B)/2`,

```text
||C-K||_(2,q)
 <=1/2||C-q||_(2,q)+1/2||C-B||_(2,q)
 <=sqrt(|H|s),
```

which is `(RDC5)`; `(RDC6)` follows by setting `s=d`.

Finally suppose the ambient representation is `lambda_H tensor I_k` and
let the complement of `q` have dimension `r=(1-beta)D`.  In each irreducible
type, at most `r` copies can have been removed.  Hence `q` contains at least
`max(0,k-r)` complete regular copies.  Their relative dimension is at least
`max(0,1-|H|(1-beta))`, proving `(RDC7)`.
