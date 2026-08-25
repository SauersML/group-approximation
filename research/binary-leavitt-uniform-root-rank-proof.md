---
rg: 2
id: binary-leavitt-uniform-root-rank-proof
kind: route
title: Sandwich a nonzero coefficient through two Steinberg commutators
target: binary-leavitt-nonzero-roots-have-uniform-corona-rank-scale
requires:
  - commuting-double-commutator-has-direct-mark-overlap
  - finite-order-normal-generation-controls-corona-rank-scale
  - involution-normal-product-forces-one-factor-overlap
  - torsion-normal-generator-has-full-support-corona-core
---

Weyl conjugacy reduces the root position to `x_13(a)` without changing the
number of normal conjugate occurrences.  First, for arbitrary `a`, the fixed
Leavitt identities give

```text
[x_41(a t_1),x_13(q)]=x_43(a t_1 q)=x_43(a t_1),
[x_43(a t_1),x_32(s_1)]=x_42(a).                       (URP1)
```

Thus `x_42(a)` is a double commutator whose inner nonconstant entry is the
marked root.  A commutator `[g,z]` is a product of two conjugates of
`z^(+/-1)`, and a commutator of that product with one more element is a
product of four conjugates.  Hence `x_42(a)` is a product of four conjugates
of `x_13(q)^(+/-1)`.

Conversely, take `a!=0`.  Binary-Leavitt single-sandwich division supplies
`u,v in L` with

```text
u a v=1.                                                (URP2)
```

Then

```text
[x_41(u),x_13(a)]=x_43(u a),
[x_43(u a),x_32(v q)]=x_42(u a v q)=x_42(q).           (URP3)
```

The same commutator expansion writes `x_42(q)` as a product of four
conjugates of `x_13(a)^(+/-1)`.  Weyl conjugacy returns both outputs to the
root positions in `(URR1)`.  Characteristic two removes all harmless
Steinberg signs.

All elementary roots have order two.  Apply
`finite-order-normal-generation-controls-corona-rank-scale` to the two
four-conjugate normal words to obtain `(URR2)--(URR3)`.

Finally reblock at the marked root using
`torsion-normal-generator-has-full-support-corona-core`.  Its active rank is
at least `d/L_0`.  The second inequality of `(URR3)` gives

```text
rank(p_a)>=rank(p_q)/4>=d/(4L_0)
```

for every fixed `a!=0`, proving `(URR4)`.

For the direct overlap, set

```text
A=x_41(a t_1),          B=x_32(s_1),
z=x_13(q),              r=x_42(a).
```

Steinberg root positions show `[r,A]=[r,B]=[r,z]=1`, while `(URP1)` says
`r=[[A,z],B]`.  Apply
`commuting-double-commutator-has-direct-mark-overlap` to obtain
`tau(p_a p_q)>=tau(p_a)/16`.  The reverse rank inequality in `(URR3)` gives
`tau(p_a)>=tau(p_q)/4`, proving `(URR5)`.  Rounded matrix representatives
have `o(1)` double-commutator and commutation discrepancies, so the robust
form gives the same two inequalities up to `o(1)`.
