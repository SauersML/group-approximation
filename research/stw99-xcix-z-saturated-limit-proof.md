---
rg: 2
id: stw99-xcix-z-saturated-limit-proof
kind: route
title: Diagonalize central copies and transport increasingly large Z windows
target: stw99-xcix-zero-distance-z-saturated-limit
requires:
  - stw99-xcix-vanishing-kk-distance-identifies-ultraproducts
---

Write `gamma_n=d_KK(A_n,B_n)` and discard an `omega`-small set so that
`gamma_n<1/12600000`.  Let `S subset P` be separable.  Choose a dense
sequence `(s^j)` in its unit ball and contraction lifts

```text
s^j=[(b_n^j)]_omega,       b_n^j in B_n.
```

Choose contractions `a_n^j in A_n` with
`||a_n^j-b_n^j||<gamma_n+1/n`.  Fix a dense sequence `(z_j)` in the unit
ball of `Z`, with `z_1=1_Z`.

The central-embedding characterization of absorption by a strongly
self-absorbing algebra gives, for each `n`, a unital embedding
`rho_n:Z->A_n` such that

```text
||[rho_n(z_j),a_n^i]|| < 1/n       (i,j<=n).
```

Apply Christensen--Sinclair--Smith--White--Winter, Corollary 4.7 in
[Perturbations of nuclear C*-algebras](https://arxiv.org/abs/0910.4953), to
transport `rho_n` to an embedding `psi_n:Z->B_n` satisfying

```text
||psi_n(z_j)-rho_n(z_j)|| < 152 sqrt(gamma_n)    (j<=n).
```

The common ultraproduct is unital because it equals `prod_omega A_n`; its
unit is `p=[(1_(A_n))]_omega`.  The estimate at `z_1=1_Z` gives

```text
[(psi_n(1_Z))]_omega=p.
```

Thus the coordinate embeddings define a unital embedding even though the
individual algebras `B_n` and maps `psi_n` need not be unital:

```text
Psi:Z -> P,       Psi(z)=[(psi_n(z))]_omega.
```

For fixed `i,j`, the commutator triangle inequality gives

```text
||[psi_n(z_j),b_n^i]||
 <= 1/n + 304 sqrt(gamma_n) + 2(gamma_n+1/n)
```

for all sufficiently large `n`.  Its ultralimit is zero.  Density of the
chosen sequences and the commutator Lipschitz estimate show that
`Psi(Z)` commutes with `S`.  Since each `psi_n` is isometric, `Psi` is
injective.  Hence `P` is Z-saturated.
