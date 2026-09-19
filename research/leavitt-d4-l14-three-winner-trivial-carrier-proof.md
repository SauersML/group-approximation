---
rg: 2
id: leavitt-d4-l14-three-winner-trivial-carrier-proof
kind: route
title: Eliminate the trivial-carrier branches of the three-winner system
target: leavitt-d4-l14-three-winner-trivial-carrier-is-fenced
requires:
  - leavitt-d4-l14-three-winner-profile-has-one-class
---

After the common carrier gives `g0=g3=1`, write

```text
p=g1,u=g2,v=g4,w=g5,x=g6,y=g7,z=g8,
a=g9,b=g10,c=g11,d=g12,e=g13.
```

If `H=1`, its unique endpoint syllables first give `a=z=1`.  The first
carrier then has two cases.  If `d!=1`, malnormality gives

```text
ep=c=1, A0=d^-1_3.
```

The alternating identities in `H` and `A0`, followed by the last carrier,
force `u=1`; direct substitution gives `K=d_3d^-1_3=1`.

If `d=1`, then `c=(ep)^-1` and `A0=1`.  The last carrier has exactly two
normal-form branches

```text
A: x=uv=1, bu=w^-1;
B: w=1, uvx=1, bu=1.
```

The remaining alternating part of `H=1` independently has exactly

```text
alpha: w=y=1, buvx=1;
beta:  buv=x=1, wy=1.
```

In `A-alpha`, `B-alpha`, and `A-beta`, imposing `A0=1` reduces the boundary
to the identity (in `A-beta`, the apparent residue is `p^-1_3`, and `A0=1`
forces `p=1`).  In `B-beta`, the equations give `b=v^2` and

```text
K=b_2v^2_0b_3.
```

This is reduced across three copies when `b!=1`, and is the identity when
`b=1`.  Hence no trivial-carrier solution has a nontrivial one-copy
boundary.
