---
rg: 2
id: projective-holonomy-rank-forces-exponential-multiplicity-proof
kind: route
title: Move the cocycle to the multiplicity factor and reduce its alternating form
target: projective-holonomy-rank-forces-exponential-multiplicity
requires: []
---

Schur's lemma factors every stable letter on the invariant isotypic block as

```text
rho(t_i)=U_i tensor V_i.
```

Because the `t_i` commute while the `U_i` obey `(PHR1)`, the multiplicity
operators satisfy the opposite projective relations

```text
V_i V_j=(-1)^(Omega_(ij)) V_j V_i.                              (PHR4)
```

Choose a change of basis over `F_2` putting the alternating form into
symplectic normal form

```text
Omega congruent to H direct-sum ... direct-sum H direct-sum 0,
H=[[0,1],[1,0]],
```

with `r` copies of `H`.  Replacing the `V_i` by the corresponding products
preserves unitarity and turns `(PHR4)` into `r` independent Pauli pairs,
commuting across distinct pairs.  Their generated complex algebra is

```text
M_(2^r)(C).
```

Therefore `C^m` is a module over `M_(2^r)(C)` and is a direct sum of copies
of its unique simple module.  This proves `2^r|m`; `(PHR3)` follows from
`dim(T)m<=d`.

For the limitation, write `m=q 2^r+s` with `0<=s<2^r`, use exact Clifford
blocks on the first `q 2^r` dimensions, and alter only the last `s`
dimensions.  The affected normalized squared HS mass is at most `2^r/m`, so
no fixed cocycle rank gives an ambient-dimension-independent obstruction.

