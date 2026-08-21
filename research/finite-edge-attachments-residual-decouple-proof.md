---
rg: 2
id: finite-edge-attachments-residual-decouple-proof
kind: route
title: Tensor the endpoint representation with left-regular finite quotients
target: finite-edge-attachments-residual-decouple
requires: []
---

Let `q_n:Gamma->Q_n` be the quotient maps.  The two assignments in `(FED3)`
agree on the amalgamated subgroup `K`, so the universal property of `(FED1)`
gives a representation `rho_n` on `(FED2)`.

The commutant of `lambda_n(Q_n)` on `ell^2(Q_n)` is the right group algebra
and has complex vector-space dimension `|Q_n|`.  Since the two tensor factors
in the first line of `(FED3)` act independently,

```text
End_(Gamma x K)(H_n)
 =End_K(V) tensor C[Q_n]^op.
```

Its dimension is `dim End_K(V)|Q_n|`; division by
`dim(H_n)^2=dim(V)^2|Q_n|^2` proves `(FED4)`.

The group `C` acts only on `V`, so

```text
End_C(H_n)=End_C(V) tensor M_|Q_n|(C).
```

After the same normalization its dimension is the positive constant in
`(FED5)`.  Finally `rho_n(p)=eta(p) tensor I`, which proves `(FED6)`.

These are exact representations satisfying every amalgam and vertex-group
relation with zero defect.  Hence no consequence of only those relations can
exclude their vanishing old-commutant density.  Any successful additional
relation must fail in this tensor model, and therefore must couple the
endpoint to a `Gamma` word outside `K` or act recursively on its residual
quotient factor.

