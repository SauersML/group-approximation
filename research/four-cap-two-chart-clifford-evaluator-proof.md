---
rg: 2
id: four-cap-two-chart-clifford-evaluator-proof
kind: route
title: Evaluate the noncentral four-cap selector charts in sixteen Clifford dimensions
target: four-cap-two-chart-mixer-has-finite-clifford-evaluator
requires:
  - edgeful-or3-four-cap-walsh-packet
---

Take the standard matrices

```text
X=[0 1;1 0],        Z=[1 0;0 -1],
H=2^(-1/2)[1 1;1 -1].                                  (TCP1)
```

They are self-adjoint involutions and satisfy

```text
XZX=-Z,             HZH=X.                              (TCP2)
```

Consequently the operators `(TCM5)` obey

```text
T^2=I,
T Z_1 T=-Z_1,
T Z_2 T=I tensor X,
[Z_2,T Z_2 T]=-I_4.                                    (TCP3)
```

After tensoring with `rho_E`, the scalar `-I_4` on `W` is the same operator
as `rho_E(J) tensor I_4`.  Equations `(TCP3)` are therefore precisely the
last three families of relations in `(TCM3)`; the tensor factors also prove
`[rho(t),rho(E)]=1`.

The restriction to `K` is faithful.  Indeed, if

```text
rho_E(e) tensor Z_1^a Z_2^b=I_16,
```

then both tensor factors are scalar.  In the four-dimensional regular
character model of `C_2^2`, no nonidentity `Z_1^a Z_2^b` is scalar.  Hence
`a=b=0`, and faithfulness of the Pauli representation gives `e=1`.  Since a
representation of the relative presentation is faithful on its displayed
copy of `K`, that copy embeds in `Gamma_2`.  It follows at once that `J!=1`
and `q!=0`.  Centrality of `J` follows from its centrality in `K` and the
relations `[t,E]=1`.

There cannot be a retraction `r:Gamma_2 -> K` fixing `K`.  If `r(t)=k`, the
relation `t z_1 t=z_1J` would give

```text
k z_1 k^(-1)=z_1J.                                     (TCP4)
```

But `z_1` is central in `K`, so the left side is `z_1`; `(TCP4)` contradicts
`J!=1`.

This no-retraction fact does not prevent a finite evaluator.  The matrices
`X,Z,H` lie in the finite two-qubit Clifford group (including its finite
scalar phase subgroup), so the image of `(TCM6)` is finite.  Finally
`rho_E(J)=-I_4` gives

```text
rho_E(p_-)=rho_E((1-J)/2)=I_4,
```

and hence `(TCM7)`.  Each character projection of `C[A]` has rank one on
`W`, so after the `E` tensor factor every cap selector has rank four.  The
finite evaluation therefore preserves the complete local four-cap packet,
not merely its central mark.
