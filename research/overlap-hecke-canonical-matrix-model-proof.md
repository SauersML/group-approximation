---
rg: 2
id: overlap-hecke-canonical-matrix-model-proof
kind: route
title: Use Bernoulli coordinate symmetries on the finite coset action and a block-swap commutator
target: overlap-hecke-coboundaries-have-canonical-finite-matrix-models
requires: []
---

Let `K=core_Lambda(M)`, `F=Lambda/K`, `P=M/K`, and `X=F/P`.  On

```text
B=(C^2)^(tensor X)
```

let `F` permute tensor coordinates, implemented by permutation unitaries
`L_f`.  Let `A` be Pauli `Z` in the base coordinate `P in X` and identity
elsewhere.  Then `A=A^*=A^(-1)`, `tr_B(A)=0`, and `A` commutes with every
`L_p`, `p in P`.  Its translates `A_x` satisfy

```text
tr_B(A_x^* A_y)=delta_(x,y),                            (OHP1)
```

because for `x!=y` the product has one trace-zero Pauli `Z` in each of two
different coordinates.

Choose finite quotients `r_j:Lambda->Q_j` which eventually separate every
fixed nonidentity element; residual finiteness supplies them.  On

```text
K_j=ell^2(Q_j) tensor B tensor C^2
```

define

```text
pi_j(g)=lambda_(Q_j)(r_j(g)) tensor L_(gK) tensor I_2,
U_j=I tensor I tensor [[0,1],[1,0]],
H_j=I tensor ( I_B tensor |0><0| + A tensor |1><1| ),
```

where `H_j=diag(I_B,A)` in the last `C^2` block coordinate (with identities
on `ell^2(Q_j)`).  Then `U_j` commutes with `pi_j(Lambda)`
and direct block multiplication gives

```text
[U_j,H_j]=I tensor A tensor I_2=:W_j.                   (OHP2)
```

The stabilizer calculation makes `W_j` commute with `pi_j(M)`.  Equation
`(OHP1)` gives `(OHC2)` exactly.  Also `tr(W_j)=tr_B(A)=0`.

Finally, for fixed `g!=1`, the quotient `Q_j` eventually has `r_j(g)!=1`,
and the normalized character of its left regular representation vanishes.
Therefore

```text
tr(pi_j(g))=tr(lambda_(Q_j)(r_j(g))) tr(L_(gK)) ->0,
```

while `tr(pi_j(1))=1`; the lattice character is canonical.  No assertion is
made that `H_j` satisfies the presentation relations of an ambient
commensurator.  That absent joint extension is exactly the arithmetic
content left open.
