---
rg: 2
id: weyl-overlap-joint-bernoulli-proof
kind: route
title: Put Pauli coordinate symmetries on the finite coset action and use one common block swap
target: weyl-overlap-coboundaries-have-joint-bernoulli-matrix-models
requires: []
---

Let `K=core_Lambda(M)`, `F=Lambda/K`, `P=M/K`, so
`X=F/P` is finite.  On

```text
B=(C^2)^(tensor X)
```

let `F` permute the tensor coordinates, with implementing unitary `L_f`,
and let `A_x` be Pauli `Z` in coordinate `x` and identity elsewhere.  Then

```text
L_f A_x L_f^*=A_(fx),
tr_B(product_r A_(x_r))
 =1 iff every coordinate occurs evenly, and is 0 otherwise.   (JBP1)
```

The stabilizer of `x` fixes its coordinate, so `A_x` commutes with its
image.

Choose finite quotients `r_j:Lambda->Q_j` separating longer and longer
nonidentity word windows.  On

```text
K_j=ell^2(Q_j) tensor B tensor C^2
```

put

```text
pi_j(g)=lambda_(Q_j)(r_j(g)) tensor L_(gK) tensor I_2,
U_j=I tensor I tensor [[0,1],[1,0]],
H_(j,x)=I tensor (I_B tensor |0><0|+A_x tensor |1><1|).
```

The block swap commutes with `pi_j(Lambda)`, and direct multiplication gives

```text
[U_j,H_(j,x)]=I tensor A_x tensor I_2=W_(j,x).          (JBP2)
```

Permutation covariance proves `(JBO1)`, the stabilizer observation proves
overlap-centrality, and `(JBP1)` proves every mixed moment in `(JBO2)`.

For fixed `g!=1`, the regular character of `Q_j` is eventually zero at
`r_j(g)`.  Hence

```text
tr(pi_j(g))
 =tr(lambda_(Q_j)(r_j(g))) tr(L_(gK)) ->0,
```

so the lattice character is canonical.  The construction is finite and
exact at every stage; its sole omitted datum is a multiplication law among
the different `H_(j,x)` lifts.

