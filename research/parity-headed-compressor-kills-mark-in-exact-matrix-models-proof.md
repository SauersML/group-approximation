---
rg: 2
id: parity-headed-compressor-kills-mark-in-exact-matrix-models-proof
kind: route
title: Compare the two conjugate finite-dimensional commutants
target: parity-headed-compressor-kills-mark-in-exact-matrix-models
requires: []
---

First form

```text
K=(Lambda x <J>) semidirect <q>,
```

where conjugation by `q` is the involutive automorphism
`g |-> J^(chi(g))g`, `J |-> J`.  Condition `(PHC1)` says that `q`
centralizes `alpha(Lambda)`.  The group in the claim is the HNN extension of
`K` identifying `Lambda` with `alpha(Lambda)`.  Britton's lemma embeds `K`,
so its nontrivial central involution `J` stays nontrivial in `H`.

Let `rho:H->U(V)` be finite-dimensional and put

```text
C_0=End_(rho(Lambda))(V),
C_1=End_(rho(alpha(Lambda)))(V).
```

Since `alpha(Lambda)<=Lambda`, restriction reverses containment and gives
`C_0<=C_1`.  Relation `(PHC2)` also gives

```text
C_1=rho(t) C_0 rho(t)^(-1).
```

Thus `C_0` and `C_1` have the same finite vector-space dimension.  The
containment is equality.  Since `q` centralizes `alpha(Lambda)`, `rho(q)`
lies in `C_1=C_0` and hence commutes with `rho(g)` for every `g in Lambda`.
Choose `p` with `chi(p)=1`.  The two conclusions

```text
rho(q)rho(p)rho(q)^(-1)=rho(p),
rho(q)rho(p)rho(q)^(-1)=rho(J)rho(p)
```

force `rho(J)=1`.

The finite-dimensionality is load-bearing: in a finite tracial von Neumann
algebra the relative commutants can satisfy a strict containment
`C_0 proper_subset u C_0 u^*`.  Their orthogonal projections live in
`B(L^2(M))`, where equal Murray--von Neumann type does not turn containment
into equality.  This is exactly why the proof cannot be passed formally to
Hilbert--Schmidt ultraproducts.

