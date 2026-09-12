---
rg: 2
id: middle-index-order-seven-orbit-closure-proof
kind: route
title: Close the ejected q-roots and compute the two Singer actions and the exact finite packet model
target: middle-index-order-seven-orbit-cut-is-native-scale-neutral
requires:
  - middle-index-marked-heisenberg-packet-is-whitehead-equivariant
  - middle-index-heisenberg-packet-is-not-center-chain-invariant
  - native-whitehead-hecke-head-has-order-seven-anchor
---

For `k in K={2,4,5,6,7,8,9}`, define coefficients

```text
r_2=r_4=r_5=r_6=q,       s_2=s_4=s_5=s_6=q,
r_7=a_1, r_8=a_2, r_9=a_3,
s_7=b_1, s_8=b_2, s_9=b_3.                             (1)
```

Prefix cancellation gives `r_ks_k=q`.  Put

```text
C_k=x_(1,k)(r_k),             D_k=x_(k,3)(s_k).        (2)
```

Different middle indices are noncomposable, while equal middle indices give
coefficient `r_ks_k=q`.  The Steinberg commutator rule therefore proves

```text
[C_k,D_l]=z^(delta_(k,l)),
[C_k,C_l]=[D_k,D_l]=1.                                 (3)
```

In particular, the four ejections `x_43(q),x_14(q),x_53(q),x_15(q)` from
the two order-seven rows are precisely the two extra pairs `(D_4,C_4)` and
`(D_5,C_5)`.  The other two center-chain ejections are the half-pairs
`C_2=x_12(q)` and `D_6=x_63(q)`; the roots `D_2=x_23(q)` and
`C_6=x_16(q)` complete them without adding an external operator.

There is a uniform matrix-unit notation for all the actors.  If

```text
E_(k,l)=x_(k,l)(s_kr_l),
```

then the six arms and the three simple center-chain roots are

```text
A_1=E_(4,7), B_1=E_(7,2),
A_2=E_(5,8), B_2=E_(8,4),
A_3=E_(6,9), B_3=E_(9,5),
x_42(q)=E_(4,2), x_54(q)=E_(5,4), x_65(q)=E_(6,5).    (4)
```

Conjugation by `E_(k,l)` sends

```text
C_k |-> C_kC_l,              D_l |-> D_lD_k,          (5)
```

and fixes the other displayed generators.  The two Whiteheads swap the
pairs `(7,8)` and `(8,9)`.  Equations `(4)--(5)` prove normalization of the
seven-pair packet by every claimed actor.

For the first order-seven word, restrict `(5)` to the ordered `C` basis
`(C_4,C_7,C_8)`.  Successive conjugation by `A_1,B_2,J_1` gives

```text
C_4 |-> C_4C_8,       C_7 |-> C_8,
C_8 |-> C_4C_7.                                      (6)
```

Its matrix is

```text
M=[[1,0,1],[0,0,1],[1,1,0]],
```

and direct multiplication gives `M^7=I` with no smaller positive power
equal to `I`.  The second row has the same matrix on `(C_5,C_8,C_9)`.

On character columns in the five-coordinate order `(4,5,7,8,9)`, the two
actions are the inverse transposes.  The first one restricts to

```text
D=[[1,1,0],[1,1,1],[0,1,0]]                           (7)
```

on `(4,7,8)`, up to the harmless choice of cyclic orientation, and the
second is the same matrix on `(5,8,9)`.  A finite orbit check is especially
short.  Encode a character by the hexadecimal mask in this five-coordinate
order.  The first cyclic orbit of `01` is

```text
01,04,05,08,09,0c,0d.                                 (8)
```

Taking the cyclic orbits of the second matrix from the seven masks in `(8)`
already gives, in addition,

```text
02,03,06,07,0a,0b,0e,0f,10,11,12,13,
14,15,16,17,18,19,1a,1b,1c,1d,1e,1f.                 (9)
```

Thus the two Singer cycles are transitive on the `31` nonzero characters.
On `P_z`, conjugation by each `D_k` flips the `k`-th `C` sign.  All joint
character atoms of the five-pair packet consequently have equal trace,
which proves `(MOF3)`.  The same argument for all seven pairs proves the
mass assertion for `E_7`.  Since the zero character is fixed by every
linear substitution `(5)` and by both swaps, `E_7` reduces all actors.
Equation `(MOF5)` follows immediately by cancellation on this reducing
corner.

For the promised finite countermodel, let `H=ell^2(F_2^7)` and set

```text
(C_k f)(x)=(-1)^(x_k)f(x),       (D_k f)(x)=f(x+e_k),
z=-I.                                                    (10)
```

For each linear actor `L` from `(4)--(5)`, let
`(U_Lf)(x)=f(L^(-1)x)`.  These signed diagonal, translation, and permutation
matrices satisfy `(3)--(6)` exactly.  The simultaneous `+1` space of all
`C_k` is `C delta_0`, and every `U_L` fixes `delta_0`.  The center-chain
subgroup `H_0=<x_65(q),x_54(q),x_42(q)>` therefore acts trivially on that
line.  Its signed character `chi`, which is negative on all three simple
roots, is orthogonal to the trivial character, proving `(MOF6)`.  This exact
finite model also shows directly that the packet relations impose no
finite-dimensional rank or capacity contradiction.
