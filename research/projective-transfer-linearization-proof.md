---
rg: 2
id: projective-transfer-linearization-proof
kind: route
title: Diagonal tensor powers turn failure of every linear transfer bound into a constant-energy leak
target: projective-transfer-linear-bound-equals-no-ultraproduct-leak
requires: []
---

`(PL2)` immediately excludes `(PL3)`.  We prove the converse by
contraposition.

Suppose `(PL2)` fails for every integer `L=n`.  Choose `(rho_n,U_n)` with

```text
e_n > n(q_n+delta_n),                                  (PL4)
```

where `e_n,q_n,delta_n` abbreviate `(PL1)`.  In particular `e_n>0`.
Put

```text
k_n=ceil(1/e_n),
rho'_n(x)=rho_n(x)^(tensor k_n),
U'_n=U_n^(tensor k_n).                                 (PL5)
```

Every word commutes with diagonal tensoring.  For each relator, telescoping
gives

```text
||rho'_n(r)-I||_2
 <= k_n ||rho_n(r)-I||_2,
```

and hence, using `k_n<=1/e_n+1`, `(PL4)`, and `e_n<=1`,

```text
delta'_n <= k_n delta_n
 <= delta_n/e_n+delta_n < 2/n.                         (PL6)
```

For a unitary word `W`, write `E(W)=1-|tr(W)|^2`.  Multiplicativity of
normalized trace and `1-(1-x)^k<=kx` for `0<=x<=1` give

```text
E(W^(tensor k))=1-(1-E(W))^k <= k E(W).                (PL7)
```

Commutator words also commute with diagonal tensoring, so summing `(PL7)`
over `S` yields

```text
q'_n <= k_n q_n < 2/n.                                 (PL8)
```

On the target word the same exact identity gives

```text
e'_n=1-(1-e_n)^k_n
    >=1-exp(-k_n e_n)
    >=1-exp(-1).                                       (PL9)
```

Equations `(PL6)`, `(PL8)`, and `(PL9)` are precisely a sequence `(PL3)`,
contradiction.  Therefore exclusion of `(PL3)` supplies some integer `L`
for which `(PL2)` holds.

Finally, assignments with defects tending to zero define a representation
of `A` in the tracial matrix ultraproduct.  The condition `q_n->0` says that
the represented class of `U_n` projectively centralizes every word in `S`,
while the lower bound in `(PL9)` says it does not projectively centralize
`h`.  Conversely every such ultraproduct leak has representing sequences
with `(PL3)`.  This proves the stated ultraproduct interpretation.  For
perfect `C` and `A`, `projective-transfer-equals-rcc-for-perfect-pairs`
then removes the scalar phases, but only within the same chosen trace class.
