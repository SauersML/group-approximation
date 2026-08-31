---
rg: 2
id: two-qutrit-proper-multipath-marginal-proof
kind: route
title: Use controlled Pauli bases and exclude every marked subgroup type
target: two-qutrit-controlled-bases-give-proper-multipath-marginal
requires:
  - finite-type-restriction-overlap-defect-formula
---

First note that each `A_a` is elementary abelian of order `27`. For
`a!=c`,

```text
A_a intersect A_c=<J,Z_1>.                              (TQM8)
```

The restrictions of `alpha_(a,b)` and `alpha_(c,d)` to this
intersection disagree on `Z_1`, so their idempotents are orthogonal by
the restriction-overlap formula. For fixed `a`, distinct `b` are
distinct characters of the same finite abelian group and are orthogonal.
Every atom is below `q` because its central character on `J` is
`omega`.

Each atom has canonical trace `1/27`. Their orthogonal sum is below `q`
and has trace `9/27=1/3=tau(q)`; faithfulness gives `(TQM3)`.
Consequently `P` and `q-P` are orthogonal projections and
`tau(P)=3/27=1/9`. This proves all equations in `(TQM3)--(TQM7)`.

We next classify the possible marked central types inside `F`. Suppose

```text
0!=z_(H,rho)<=q,                H<=F.                    (TQM9)
```

Since `Jq=omega q`, one has `Jz_(H,rho)=omega z_(H,rho)`. The
identity coefficient of the central idempotent is
`dim(rho)^2/|H|>0`. Comparing the coefficient at `J` forces `J in H`,
and Schur's lemma gives `rho(J)=omega I`.

Put `W=H/Z<=F/Z isomorphic to F_3^4`, equipped with the symplectic
commutator form, and let `R=rad(W)` have dimension `k`. Its inverse
image `R_tilde` is the center of `H`. The elementary finite Heisenberg
character calculation says that a marked irreducible `rho` has degree
`3^r`, where

```text
dim(W)=2r+k,
```

and its character vanishes off `R_tilde` while equalling
`3^r lambda` on `R_tilde`, for one character
`lambda:R_tilde->T` extending `J |-> omega`. Expanding the central
idempotent therefore gives

```text
z_(H,rho)
 =(3^(2r)/3^(1+2r+k))
   sum_(h in R_tilde) conjugate(lambda(h)) h
 =e_(R_tilde,lambda).                                  (TQM10)
```

In the nine-dimensional marked spin block its rank is

```text
9/3^k.                                                  (TQM11)
```

In particular, a marked central type of rank three must be the common
eigenspace of one noncentral Pauli element spanning the one-dimensional
radical `R`.

We show that `P` has no such scalar Pauli. In the marked spin
representation write

```text
H_spin=C^3 tensor C^3.
```

Let `|a>` be the `omega^a` eigenvector of `Z_1`, and let
`|psi_a>` be the eigenvalue-one vector of

```text
B_0=Z_2,             B_1=X_2,             B_2=X_2 Z_2.
```

Then

```text
Ran(P)=span{|a> tensor |psi_a>:a in F_3}.               (TQM12)
```

Suppose the Pauli word

```text
U=J^c X_1^u Z_1^v X_2^s Z_2^t                         (TQM13)
```

acts as a scalar on this range. The factor `X_1^u` shifts the three
`Z_1` eigenspaces, so scalar action forces `u=0`. The second-qutrit
Pauli `X_2^s Z_2^t` must then have both `|psi_0>` and `|psi_1>` as
eigenvectors. These vectors come from the `Z_2` and `X_2` bases, so
they have nonzero inner product and are not proportional. A nonidentity
qutrit Pauli has three simple eigenvalues; two of its eigenvectors are
therefore either proportional or orthogonal. Hence `s=t=0`. Finally
`Z_1^v` has eigenvalues `omega^(va)` on the three displayed vectors,
so scalar action forces `v=0`. Only the central powers of `J` act
scalarly. Equations `(TQM10)--(TQM11)` now show that `P` is not a
central finite type of any subgroup of `F`.

This also excludes every transported finite type in `Gamma`. Indeed, a
finite subgroup of `Gamma=K *_Z F` fixes a vertex of the Bass--Serre
tree. The coefficient of `Z_2` in `P` is `1/27`, contributed by
`p_(0,0)`, so any subgroup whose central idempotent equals `P` contains
`Z_2`. A vertex stabilizer distinct from the displayed copy of `F`
intersects it only in `Z`, and cannot contain `Z_2`. Thus the subgroup
must lie in `F`, where it was just excluded. This proves `(TQM6)`.

Finally, `q C[F]q` is the full marked spin block `M_9(C)`. Since
`P` has rank three, it is neither zero nor `q` and is noncentral.
Bass--Serre theory makes the finite amalgam `Gamma` virtually free. Thus
the construction solves exactly the local algebraic multipath problem but
remains a hyperlinear, finite-dimensional-visible boundary model.
