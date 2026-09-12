---
rg: 2
id: finite-packet-flat-morita-cycle-countermodel-proof
kind: route
title: Tensor the multipath projection with a three-cycle of matrix units
target: flat-morita-three-cycles-do-not-glue-multipath-marginals
requires:
  - two-qutrit-controlled-bases-give-proper-multipath-marginal
---

The marked Heisenberg corner `r C[L] r` is a full `3 by 3` matrix
algebra, so its matrix units are finite group-algebra expressions. Therefore
all elements in `(MTC1)--(MTC4)` belong to the algebraic corner
`Q C[F times L] Q`.

The matrix-unit equations give, for indices modulo three,

```text
(P tensor E_(i+1,i))^*(P tensor E_(i+1,i))
 =P tensor E_ii=P_i,

(P tensor E_(i+1,i))(P tensor E_(i+1,i))^*
 =P tensor E_(i+1,i+1)=P_(i+1).
```

They also give

```text
v_2 v_1 v_0
 =P tensor E_02 E_21 E_10
 =P tensor E_00=P_0.
```

This proves `(MTC3)`. In particular the partial isometries make all
`P_i` Murray--von Neumann equivalent, so their `K_0` classes and traces
agree.

The three diagonal matrix units are orthogonal. Hence the projections
`P_i` are orthogonal and nonzero, proving `(MTC6)`. Put

```text
R_i=Q-P_i-P_(i+1).
```

The three terms `v_i`, `v_i^*`, and `R_i` have mutually orthogonal
initial and final supports. Consequently

```text
S_i^*=S_i,
S_i^2=v_i^*v_i+v_iv_i^*+R_i=P_i+P_(i+1)+R_i=Q.
```

Multiplying once more gives `S_iP_iS_i=P_(i+1)`, so every Steinberg swap
relation in `(MTC5)` holds.

Finally, `F times L` is finite and `Q=q tensor r` is a nonzero central
finite-group type projection. Its finite-dimensional marked block is an
exact representation of every displayed relation, while `P_0,P_1,P_2`
remain pairwise orthogonal. A formal consequence of the arrow, swap, and
flat-return relations would hold in this model; marginal equality does not.
Therefore it is not such a consequence. Only an additional relation outside
that Morita presentation can impose equality.
