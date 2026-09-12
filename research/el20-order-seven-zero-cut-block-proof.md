---
rg: 2
id: el20-order-seven-zero-cut-block-proof
kind: route
title: Compute the incompatible Hecke character commutator on seven equivalent Leavitt corners
target: el20-order-seven-heads-force-zero-common-hecke-reducing-cut
requires:
  - native-whitehead-hecke-head-has-order-seven-anchor
  - center-chain-mixed-hecke-overlap-is-common-pauli-source
  - middle-index-order-seven-orbit-cut-is-native-scale-neutral
---

Put

```text
p_2=p_4=p_5=p_6=q,
p_7=e_0=s_0t_0,       p_8=e_(00),       p_9=e_(000).
```

The seven right modules `p_jR`, in the ordered index list

```text
(2,4,5,6,7,8,9),                                      (1)
```

are all identified with `qR`.  Incoming and outgoing coefficient roots
can be chosen as

```text
C_j=x_(1,j)(r_j),       D_j=x_(j,3)(s_j),
r_2=r_4=r_5=r_6=s_2=s_4=s_5=s_6=q,
(r_7,r_8,r_9)=(a_1,a_2,a_3),
(s_7,s_8,s_9)=(b_1,b_2,b_3).                          (2)
```

Since `r_js_j=q`, the fourteen roots in `(2)` form a seven-pair
extraspecial group with center `z`.  Every middle-block root used below is
a binary transvection on the seven coordinates in `(1)` and is the
identity off their corner sum.

On incoming coefficient columns, a middle root from coordinate `i` to
coordinate `j` acts as

```text
E_(i->j)=I+e_j e_i^*.                                  (3)
```

For example `a_2b_2=q`, `a_3b_3=q`, and `q^2=q`, so the three roots in
`(OZC1)` act as

```text
h=I+e_2e_4^*,       d=I+e_2e_8^*,       f=I+e_4e_9^*. (4)
```

The remaining roots of `L_0` act by the transvections associated to

```text
6->5, 5->4, 4->2, 8->2, 9->4, 9->2,
9->7, 5->7, 6->7, 6->8.                               (5)
```

All coefficient checks reduce to
`q a_m=a_m`, `a_mb_m=q`, and prefix cancellation.  Thus `(3)--(5)` are
equalities of the actual elementary matrices, not an abstract quotient.

Let

```text
N=[[1,0,1],[0,0,1],[1,1,0]] in GL_3(F_2).             (6)
```

The block calculation in `native-whitehead-hecke-order-seven-proof` gives
`M=JBA`; conjugation of incoming rows is by
`N=(M^(-1))^T`.  Hence `t_1` acts by `N` on `(4,7,8)` and fixes the other
four coordinates, while `t_2` acts by `N` on `(5,8,9)` and fixes the
others.  Denote these two seven-dimensional matrices by `N_1,N_2`.

Set

```text
A=(N_1^2N_2)(I+e_2e_8^*)(N_1^2N_2)^(-1),
B=(N_1^(-2)N_2N_1^(-1))(I+e_4e_9^*)
  (N_1^(-2)N_2N_1^(-1))^(-1).                         (7)
```

Direct multiplication over `F_2`, in the basis `(1)`, gives

```text
A=I+e_2(e_4^*+e_5^*+e_7^*+e_8^*+e_9^*),
B=I+e_7e_4^*,
[A,B]=I+e_2e_4^*.                                     (8)
```

Equations `(4)` and `(8)` prove the exact group identity `(OZC3)`.  If
`E<=Q` reduces `t_1,t_2`, it reduces every word in them.  Since `dE=fE=E`,
both conjugates in `(OZC3)` restrict to the identity on `E`; but `hE=-E`.
Therefore `E=0`.

Finally, the commuting `C_j` have `2^7` joint atoms on the `z=-1` sector,
and conjugation by `D_j` flips the `j`-th sign.  All atoms consequently
have equal trace.  The trivial-character atom is fixed by every binary
linear actor in `(3)--(6)`, in particular by `t_1,t_2` and `L_0`.  Since
`lambda_0` is nontrivial on `h`, its signed Reynolds projection annihilates
that atom.  This proves the arbitrary-profile interpretation and completes
the claim.
