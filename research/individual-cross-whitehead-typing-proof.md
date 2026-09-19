---
rg: 2
id: individual-cross-whitehead-typing-proof
kind: route
title: Expose the nonconstant Hecke image of each partial branch swap
target: individual-cross-whiteheads-miss-native-hecke-target
requires:
  - cross-branch-partial-whiteheads-have-finite-wreath-gauge-model
  - literal-whiteheads-give-gauged-moving-bridge-table
---

On ordered coordinates `(7,8)`, the two individual cross-branch words have
blocks

```text
K_0=[[q_1,p],[r,q_0]],       K_1=[[q_0,r],[p,q_1]].   (IKTP1)
```

Conjugating `h=x_28(1)` by an involutory block only multiplies its row vector
on the right by that block.  The second rows in `(IKTP1)` are respectively
`(r,q_0)` and `(p,q_1)`, proving `(IKT2)`.  Every element of `L_0` is a
product of matrices over the embedded `F_2`, whereas `p,r,q_0,q_1` are
nonconstant reduced Leavitt matrix units.  The two displayed entries occur
in different matrix positions, so no cancellation is possible.  This
proves the first nonnormality assertion.

The native block `(IKT3)` acts on a row `(a,b)` by

```text
(a,b)J_1=(a(1-q_0)+b x_1, a y_1+b(1-e_00)).          (IKTP2)
```

The binary prefix relations give

```text
r(1-q_0)=0,       q_0x_1=x_1,
ry_1=s_1t_00,     q_0(1-e_00)=q_0+e_00,              (IKTP3)

p(1-q_0)=p,       q_1x_1=0,
py_1=0,           q_1(1-e_00)=q_1.                   (IKTP4)
```

Substitution in `(IKTP2)` proves `(IKT4)`.  The entries `x_1`,
`s_1t_00+q_0+e_00`, `p`, and `q_1` are nonconstant reduced Leavitt
expressions, so
the same constant-matrix argument proves `(IKT5)`.  By the established
native bridge table, `v_1` normalizes the signed pair and
`t_1=J_1v_1`.  Therefore

```text
t_1^(-1)K_i=v_1^(-1)J_1K_i
```

belongs to the signed normalizer if and only if `J_1K_i` does.  This proves
`(IKT6)`.

The constant Weyl has block `[[0,1],[1,0]]`.  Swapping both rows and columns
in `(IKTP1)` interchanges `K_0` and `K_1`, proving `(IKT7)` together with
`T=K_0K_1`.

Finally, in `S_4` the double transpositions form a normal Klein four group.
Conjugation by `D=(1 2)` exchanges

```text
(1 3)(2 4)  and  (1 4)(2 3)
```

and fixes their product `(1 2)(3 4)`.  The transpositions
`D=(1 2),E=(2 3),F=(1 3)` satisfy both native `S_3` braid equations, while
`DE` has order three.  This verifies every row of `(IKT8)--(IKT9)` and
completes the scoped fence.
