---
rg: 2
id: iwahori-dual-fusion-firewall-proof
kind: route
title: Square restriction by Frobenius reciprocity and freeze the congruence-kernel orbit
target: iwahori-dual-inclusion-graph-is-fusion-not-the-bruhat-tits-tree
requires: []
---

Frobenius reciprocity and the tensor identity give, for
`pi,sigma in Irr(G_a)`,

```text
<Res pi,Res sigma>_(B_a)
 = <pi,Ind Res sigma>_(G_a)
 = <pi,sigma tensor Ind(1_(B_a))>_(G_a).
```

Since `Ind(1_(B_a))=C[G_a/B_a]=P_a`, this is `(DIF2)`. The dimension
identity

```text
sum_pi <pi,sigma tensor P_a> dim(pi)=3dim(sigma)
```

shows that the dimension vector is a Perron vector of eigenvalue three.

Because `B_a` is the inverse image of a point stabilizer in `S_3`, the
coset action factors through `S_3`, proving `(DIF3)`. On `K_a`, therefore,

```text
(sigma tensor P_a)|_(K_a)=3 sigma|_(K_a).              (DFP1)
```

Clifford theory says the irreducible constituents of `sigma|_(K_a)` form
one `G_a`-orbit. If `pi` occurs in `sigma tensor P_a`, `(DFP1)` forces the
same orbit for `pi`. This proves sector closure. Applying the dimension
identity inside one closed component proves `(DIF4)`.

For completeness, write the newest-layer Lie algebra as triples

```text
X(a,b,c)=[[a,b],[c,a]] in sl_2(F_2).
```

For an upper transvection `u` and the Weyl element `w`, conjugation acts by

```text
u:(a,b,c)->(a+c,b+c,c),       w:(a,b,c)->(a,c,b).
```

On dual coordinates `(alpha,beta,gamma)` the action is

```text
u:(alpha,beta,gamma)->(alpha,beta,alpha+beta+gamma),
w:(alpha,beta,gamma)->(alpha,gamma,beta).
```

Its orbits are

```text
{(0,0,0)},
{(1,1,1)},
{(1,0,0),(1,0,1),(1,1,0)},
{(0,1,0),(0,1,1),(0,0,1)},
```

which proves `(DIF5)`.

