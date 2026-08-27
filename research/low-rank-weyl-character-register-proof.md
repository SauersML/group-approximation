---
rg: 2
id: low-rank-weyl-character-register-proof
kind: route
title: Realize the low-rank form on qubits and orthogonalize its labels by characters
target: low-rank-weyl-tables-have-polynomial-models
requires:
  - bounded-prefix-decision-cost-forces-bounded-approximate-rank
---

Factor

```text
K'_(u,v)=<a_u,b_v>,       a_u,b_v in F_2^r,
```

and pad to `r_0=max(r,2)`.  On `r_0` qubits let `P(a)` and `Q(b)` be the
standard commuting translation and phase Weyl families, so

```text
[P(a),Q(b)]=(-I)^<a,b>.
```

Choose a binary group `L` of order less than `2(D+1)` having at least `D`
distinct nontrivial characters.  Let `C_u` and `D_v` be the corresponding
diagonal character involutions on two separate copies of `ell^2(L)`.

On

```text
H_-= (C^2)^(tensor r_0) tensor ell^2(L) tensor ell^2(L)
```

put

```text
J=-I,
X_u=P(a_u) tensor C_u tensor I,
Y_v=Q(b_v) tensor I tensor D_v.
```

This realizes `K'` exactly.  The nontrivial character factors make every
named generator traceless and make distinct labels orthogonal, irrespective
of repeated rows in the rank factorization.

Take an equally dimensional positive sector.  On its first qubit factor
choose two commuting trace-zero involutions `R,S` with `tr(RS)=0` (two
qubits suffice), let the unused qubits be spectators, and put

```text
J=I,
X_u=R tensor C_u tensor I,
Y_v=S tensor I tensor D_v.
```

All cross relations are exact there because `J=I`.  The direct sum of the
two sectors gives `(LAR2)` and `tr(J)=0`.  Its dimension is
`2·2^r_0 |L|^2`, bounded by `(LAR1)`.

Where `K=K'`, `(LAR3)` is exact.  At an edited entry, only the negative half
has the wrong scalar commutator; its full-space normalized squared defect is
`(1/2)·4=2`.  Averaging over at most `epsilon D^2` edited entries gives
`2 epsilon`.  Finally the two equal central sectors give
`||J-I||_2^2=(1/2)·4=2`.
