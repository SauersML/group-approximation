---
rg: 2
id: aggregate-morita-cross-partial-whitehead-gl3-wreath-proof
kind: route
title: Stabilize one cross partial Whitehead and exchange the returned rank-three packets
target: aggregate-morita-cross-partial-whitehead-has-gl3-wreath-model
requires:
  - aggregate-morita-common-opposite-return-has-gl3-square-model
  - cross-branch-partial-whiteheads-have-finite-wreath-gauge-model
---

Write `q_i=s_it_i`, `p=s_0t_1`, and `r=s_1t_0`.  The binary Leavitt
relations give

```text
pr=q_0,       rp=q_1,
q_1s_0=0,    rs_0=s_1,
t_1r=t_0,    t_1q_0=0.                                (MCPP1)
```

On the ordered coordinates `(7,8)`, the partial Whitehead in `(MCP3)` is

```text
K=[[q_1,p],[r,q_0]].                                  (MCPP2)
```

The same coefficient relations show `K^2=1`.  Acting on the column
coefficient of `S_0=x_79(s_0)` gives

```text
K [s_0,0]^t=[0,s_1]^t,
```

and acting on the row coefficient of `T_1=x_(10,8)(t_1)` gives

```text
[0,t_1] K=[t_0,0].                                    (MCPP3)
```

Consequently

```text
KS_0K=x_89(s_1),       KT_1K=x_(10,7)(t_0).           (MCPP4)
```

The constant Whitehead `P` exchanges coordinates `9,10` and commutes with
`K`, whose support is `(7,8)`.  Conjugating `(MCPP4)` by `P` therefore
gives

```text
HS_0H=x_(8,10)(s_1)=U_1,
HT_1H=x_97(t_0)=V_0.                                  (MCPP5)
```

Since `H^2=1`, the reverse two rows in `(MCP4)` follow as well.  Notice
that these are conjugacies of the literal native occurrences from the
aggregate Morita table, not an analytic identification of two abstract
operators.

For the complementary partial Whitehead

```text
K'=[[q_0,r],[p,q_1]],
```

the same calculation gives

```text
K'S_1K'=x_(8,10)(s_0),
K'T_0K'=x_97(t_1).                                    (MCPP6)
```

The two partial Whiteheads commute and their product is

```text
KK'=[[0,u],[u,0]],             u=p+r,
```

as established in
`cross-branch-partial-whiteheads-have-finite-wreath-gauge-model`.
Left multiplication by this block sends `(s_i,0)^t` to
`(0,s_(1-i))^t`, and right multiplication sends `(0,t_i)` to
`(t_(1-i),0)`.  The coordinate swap `P` then gives every arm row in
`(MCP6)`.  Taking commutators gives

```text
JC_iJ=[U_(1-i),V_(1-i)]=R_(1-i).                      (MCPP7)
```

Finally, disjoint support makes `P` commute with `K,K'`, so

```text
HJ=(PK)(PKK')=K',                                     (MCPP8)
```

which is the exact comparison row `(MCP7)`.

For the finite model, the six transvections in `(MCP8)` satisfy the
matching commutator and parent-braid relations by
`aggregate-morita-common-opposite-return-has-gl3-square-model`.  The
coordinate-reversal automorphism of `GL_3(F_2)` sends

```text
e_12 -> e_32,       e_23 -> e_21,       e_13 -> e_31,
```

and is involutive.  Swapping the two factors while applying this
automorphism defines the element `j` in `(MCP10)`.  Adjoining a central
involution `z` and using `(MCP11)` makes both `H` and `J` implement the same
packet swap, but records their exact relative word as the surviving gauge
`z`.  The remaining assignments in `(MCP11)` also verify
`H=PK`, `T=KK'`, and `J=PT` exactly.  Substitution proves `(MCP4)`,
`(MCP6)`, and `(MCP7)`, while the base
`K_3 times K_3` still verifies every old row and keeps `C_1` nonidentity.
The left regular representation of the resulting finite group is therefore
an exact finite-dimensional unitary model of the enlarged occurrence table.

The model deliberately does not claim that all elementary subwords of
`H=PK` have been closed under every relation of `EL_20(R)`.  It proves the
sharp implication needed here: the literal word and the four native-arm
covariances which make the first partial mixer a cross-packet occurrence,
together with the full packet-swap and comparison rows, still admit a
marked finite model.  A positive lock needs an additional relation not
implied by this transport table.
