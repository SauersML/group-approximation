---
rg: 2
id: support-packet-covariant-wedderburn-detector
kind: claim
title: A seven-dimensional packet coefficient is allowed-flat but has forbidden Wedderburn holonomy
artifacts:
  - experiments/schur_packet_tensor_fusion_search.py
  - experiments/schur_packet_wedderburn_holonomy_opt.py
  - research/artifacts/support-packet-covariant-wedderburn-detector-2026-08-20.md
distinct_from:
  predicate-rank-jump-forces-adjoint-reynolds-gap: that compares the commutants of the nested packet groups in one representation; this compares diagonal tensor coefficients related by one explicit packet automorphism and is exactly flat on all allowed selector sectors.
  commuting-automorphism-cocycle-forces-multiplicity: that extracts a fixed divisibility condition from a projective square; this gives an amplification-stable distance between nonisomorphic commutant algebras.
  full-center-hnn-transport-cancels-schur-multiplicity: that proves ordinary full-center Pauli restriction loses the ambient rank jump; this retains it through the full packet fusion ring and detects it as Wedderburn block shape.
---

Let `B_sub` be the order-128 fixed support packet with central basis
`(J,z_e,z_f)` and commutators

```text
[p_1,q_1]=J,       [p_1,q_2]=J z_e,
[p_2,q_1]=z_f,     [p_2,q_2]=1.                     (CWD1)
```

There is an involutive automorphism `alpha` given by

```text
alpha(J)=z_e, alpha(z_e)=J, alpha(z_f)=z_f,
alpha(p_i)=p_i,
alpha(q_1)=q_1 q_2, alpha(q_2)=q_2.                 (CWD2)
```

Write `T_k` for the unique four-dimensional packet simple with central
character `k` when `k` is `011` or `101`, and write `1` for the trivial
simple.  Put

```text
V_+ = 1^3 directSum T_011,
V_- = 1^3 directSum T_101.                           (CWD3)
```

Both coefficients have dimension seven, and `V_-` is the pullback of `V_+`
by `alpha`.

For every irreducible packet `S` in the `J=-1` allowed central sectors
`100,110,111`, the commutant algebras

```text
End_B(S tensor V_+),       End_B(S tensor V_-)       (CWD4)
```

are unitarily conjugate.  Their Wedderburn signatures `(multiplicity,
simple dimension)` are

```text
k=100 or 111:  (1,2)^4, (3,2),
k=110:         (2,4), (3,2).                         (CWD5)
```

On the forbidden simple `S=T_101`, however,

```text
End_B(T_101 tensor V_+)  = M_(2m)^4 directSum M_(3m),
End_B(T_101 tensor V_-)  = M_m^16    directSum M_(3m) (CWD6)
```

after amplification by multiplicity `m`.  The corresponding packet simples
have dimensions `(2,2,2,2,4)` on the plus side and `(1^16,4)` on the minus
side.  In particular the two algebras have the same vector-space dimension
`25m^2`, but are not isomorphic: their centers have dimensions five and
seventeen.

More quantitatively, let `R_+,R_-` be their Reynolds projections on the
adjoint space of dimension `(28m)^2`.  For every unitary `W` on the underlying
`28m`-dimensional Hilbert space,

```text
||R_+-Ad_W R_- Ad_W^*||_(HS,(28m)^2)^2 >= 1/49.      (CWD7)
```

Thus this cell is simultaneously:

- exactly flat on every allowed selector sector;
- related by one fixed packet automorphism, so it has a group-covariance
  interface; and
- separated by a universal adjoint-HS constant on the forbidden sector,
  even after arbitrary multiplicity amplification.

It is the first explicit finite covariance coefficient in the Schur--Clifford
route that passes the equal-Hilbert-capacity and allowed-sector falsification
tests.
