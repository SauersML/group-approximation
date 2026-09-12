---
rg: 2
id: a4-coherence-fan-canonically-splits-multiplicity-proof
kind: route
title: Gauge each C3 sector through the common C2 carrier
target: a4-coherence-fan-canonically-splits-multiplicity
requires:
  - a4-regular-three-way-coherence-transducer
---

The three projections `R_j` are mutually orthogonal and the transducer theorem
gives unitary maps `T_j:R_j H -> S H`.  Hence the displayed map `W` is unitary
from their direct sum `R H` onto `C^3 tensor S H`.

On `R_j`, the order-three generator acts by the scalar `omega^j`, because
`R_j<=P_j`.  Therefore

```text
W rho(a) W^* = diag(1,omega,omega^2) tensor I_S.
```

For the involution, compute its `(j,k)` block after conjugating by `W`.  If
`j=k`, `a4-regular-three-way-coherence-transducer` gives

```text
R_j rho(b) R_j = -(1/3)R_j,
```

so the transformed diagonal block is `-(1/3)I_S`.  If `j!=k`, the same theorem
gives

```text
(3/2)R_j rho(b) R_k=T_j^*T_k.
```

Multiplying on the left by `T_j` and on the right by `T_k^*` yields

```text
T_j R_j rho(b) R_k T_k^*=(2/3)I_S.
```

Thus every off-diagonal block is `(2/3)I_S`, proving the claimed tensor form.
The matrix `B=(2/3)J-I_3` is a self-adjoint involution, and together with the
diagonal order-three matrix it is the standard three-dimensional A4 irrep.
All dependence on the number of regular copies has therefore been isolated in
the tensor factor `S H`.