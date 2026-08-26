---
rg: 2
id: exact-kazhdan-radical-kernel-cannot-be-lef-proof
kind: route
title: Combine the finite-residual bound with the Ozawa--Thom quotient theorem
target: exact-kazhdan-radical-kernel-cannot-be-lef
requires:
  - mapping-torus-mf-radical-lies-in-finite-residual
  - lef-implies-operator-mf
---

First prove the general assertion `(EKL2)`.  Let `K` be countable, LEF and
Kazhdan, and suppose every homomorphism from `K` to a finite group is trivial.
By `lef-implies-operator-mf`, `K` is operator-MF.  Dadarlat,
*Obstructions to matricial stability of discrete groups and almost flat
K-theory*, arXiv:2007.12655v2, states in the introduction that every MF group
is weakly quasidiagonal.  Proposition 3.19 of that paper, attributed there to
Ozawa--Thom, states that an infinite weakly quasidiagonal property-`(T)` group
has an infinite residually finite quotient `q:K -> Q`.

If `K` were infinite, choose `x!=1` in `Q`.  Residual finiteness of `Q`
provides a finite group `F` and a homomorphism `f:Q -> F` with `f(x)!=1`.
Then `f o q` is a nontrivial finite quotient of `K`, a contradiction.  Hence
`K` is finite.  If it were nontrivial, its identity homomorphism would itself
be a nontrivial homomorphism to a finite group.  Therefore `K=1`.

Now assume `(EKL1)`.  Property `(T)` makes `K` finitely generated, hence
countable.  The consequence `(FRB2)` of
`mapping-torus-mf-radical-lies-in-finite-residual` gives

```text
R_fin(K)=K,
```

which says precisely that every finite quotient of `K` is trivial.  If `K`
were LEF, `(EKL2)` would give `K=1`.  Contrapositively, every nontrivial exact
Kazhdan radical kernel is not LEF.

A marked limit of finite groups is LEF.  Applying the conclusion to any
property-`(T)` marked limit with no nontrivial finite quotient proves the
announced exclusion of the alternating-mother program.  In particular, an
infinite simple marked limit cannot occur there: simplicity would eliminate
all nontrivial finite quotients, contradicting `(EKL2)`.
