---
rg: 2
id: native-whitehead-corner-collapses-hecke-flags
kind: claim
title: Common native-Whitehead reduction collapses the two center-chain Hecke flags
invalidates:
  - native-prefix-whiteheads-restrict-to-center-chain-hecke-flags
artifacts:
  - research/chained-native-whitehead-polar-proof.md
distinct_from:
  same-center-whitehead-gram-is-not-native-selector-gram: that observes that the two common-center Whitehead label actions are both quarter swaps and hence do not authenticate the unequal selector pair; this computes their exact action on the new nested Hecke support and proves that every common reducing subcorner kills the Hecke distinction itself.
  center-chain-hecke-polar-supports-are-nested-pauli-flags: that obtains a positive common Pauli corner and distinct quarter/eighth Hecke supports; this shows why the two obvious native Whitehead words cannot be attached to those supports by restriction.
  center-chain-hecke-flags-authenticate-native-occurrences: that allows any fixed mixed occurrence row identifying the native transports with the Hecke polars; this refutes only the natural direct-compression route, not every possible occurrence compiler.
---

Use the chained packet

```text
A_1=x_47(a_1),        A_2=x_58(a_2),
B_1=x_72(b_1),        B_2=x_84(b_2),        B_3=x_95(b_3)
```

and put

```text
x_1=b_2a_1=s_(00)t_0,       y_1=b_1a_2=s_0t_(00),
x_2=b_3a_2=s_(000)t_(00),   y_2=b_2a_3=s_(00)t_(000). (CNW1)
```

In characteristic two the two native partial-Whitehead words are exactly

```text
J_1=x_87(x_1)x_78(y_1)x_87(x_1),
J_2=x_98(x_2)x_89(y_2)x_98(x_2).                       (CNW2)
```

Prefix cancellation gives `y_i x_i=e_(0^i)` and
`x_i y_i=e_(0^(i+1))`, so `J_i^2=1`.  Both words centralize `H` and hence
`e=e_chi`.

Retain the notation

```text
v=x_57(a_1),  w=x_67(a_1),  r=x_58(a_2),
s=x_68(a_2),  t=x_59(a_3),  l=x_69(a_3),
p_2=e z_<v,w,s>.                                      (CNW3)
```

Direct block conjugation gives

```text
J_1:(v,r)(w,s),             J_2:(r,t)(s,l),            (CNW4)
```

with all undisplayed generators fixed.  Therefore neither word normalizes
`p_2`.  Their exact compressions are self-adjoint partial isometries

```text
p_2J_1p_2=J_1q_1,   q_1=e z_<v,r,w,s>,
p_2J_2p_2=J_2q_2,   q_2=e z_<v,w,s,l>,                 (CNW5)
```

and

```text
(p_2J_i p_2)^*(p_2J_i p_2)=q_i,
tau(q_1)=tau(q_2)=(1/16)tau(e)=1/1024.                (CNW6)
```

Thus their polar-support masses are equal and match neither the
quarter/eighth Hecke pair.

There is a positive common reducing corner, but it destroys the desired
distinction.  Put

```text
N=<v,r,t,w,s,l> ~= F_2^6,          p_*=e z_N.          (CNW7)
```

Then `p_*` is the meet of all `S_3=<J_1,J_2>` conjugates of `p_2`, so it is
the largest subprojection of `p_2` reducing both Whiteheads.  Its trace is

```text
tau(p_*)=(1/64)tau(e)=1/4096.                          (CNW8)
```

Since `r=A_2` belongs to `N`,

```text
A_2p_*=p_*,
(eA_1e)p_*=A_1p_*=(eA_2A_1e)p_*.                      (CNW9)
```

Indeed `(CNW9)` holds on every common reducing subprojection of `p_2`,
because every such projection lies below `p_*`.  Hence the two distinct
Hecke polars become the same map on precisely the corners on which both
native Whiteheads are simultaneously defined as unitaries.

Their label actions do not collapse.  The three same-center Pauli pairs

```text
(x_47(a_1),x_72(b_1)),
(x_48(a_2),x_82(b_2)),
(x_49(a_3),x_92(b_3))                                  (CNW10)
```

reduce `p_*`, cross-commute, and all have central commutator
`x_42(q)=-1`.  Thus

```text
p_*H=(C^2)^(tensor 3) tensor M,
J_1p_*=SWAP_(1,2) tensor V_1,
J_2p_*=SWAP_(2,3) tensor V_2,                          (CNW11)
```

where the two reservoir involutions obey the Coxeter braid.  The polar maps
in `(CNW11)` are the displayed full unitaries, and both fixed label actions
have negative fraction `1/4`.  They are distinct: in the canonical regular
model `J_1J_2` lies in the nontrivial order-three coset of the finite
`S_3` quotient, so

```text
||(J_1-J_2)p_*||_2^2=2tau(p_*).                        (CNW12)
```

Equations `(CNW9)--(CNW12)` are an exact finite countermodel to the proposed
identification.  The two native Whiteheads remain distinct adjacent swaps
exactly where the two Hecke polars have become equal.

DERIVATION
chained-native-whitehead-polar-proof
