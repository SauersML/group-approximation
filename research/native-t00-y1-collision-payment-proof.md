---
rg: 2
id: native-t00-y1-collision-payment-proof
kind: route
title: Sandwich the same-root discrepancy and telescope its normal word
target: native-t00-y1-collision-pays-marked-opnorm
requires:
  - row2-parallel-a2-return-diamond-has-gl8-model
  - binary-leavitt-nonzero-roots-have-uniform-corona-rank-scale
---

Root additivity in characteristic two gives `D=TY=x_78(d)`.  The Leavitt
prefix relations give

```text
t_00s_00=1,                  (s_0t_00)s_00=s_0,
t_1s_0=0,                    t_1s_1=1.
```

They imply `(TYC2)`, so in particular `d!=0`.

Conjugate `D` by a constant Weyl word to `x_13(d)`.  The ordinary Steinberg
commutator law gives

```text
[x_41(t_1),x_13(d)]=x_43(t_1d),
[x_43(t_1d),x_32(s_00s_1q)]
 =x_42(t_1d s_00s_1q)=x_42(q).                        (1)
```

This proves `(TYC3)`.  A commutator `[U,V]` is the product of two
conjugates of `V` or `V^(-1)`.  The double commutator in `(1)` is therefore
a product of four conjugates of `D`; the outer Weyl words do not change the
count.

For any unitaries `V_1,...,V_4`,

```text
||V_1V_2V_3V_4-I||_op <=sum_i ||V_i-I||_op.           (2)
```

Each conjugate of `rho(D)` has distance `||rho(D)-I||_op` from the
identity.  Apply `(2)` to the normal word for `rho(z)` to obtain

```text
||rho(z)-I||_op<=4||rho(D)-I||_op.                    (3)
```

Finally `T,Y` are involutions in one abelian root subgroup, so

```text
(rho(T)-rho(Y))rho(Y)=rho(TY)-I=rho(D)-I.
```

Right multiplication by a unitary preserves operator norm.  Combining
this equality with `(3)` proves `(TYC4)`.  Fixed-word telescoping absorbs
operator-norm microstate defects into `o(1)`, proving `(TYC5)`.

The coefficient `d` is nonzero by `(TYC2)`, and the position `(7,8)` is
disjoint from the marked position `(1,3)`.  Apply `(URR5)` from
`binary-leavitt-nonzero-roots-have-uniform-corona-rank-scale`, after the
constant Weyl permutation fixing `1,3` and carrying its displayed output
position to `(7,8)`.  This gives `(TYC6)`.  The two root involutions commute,
so `P_zP_D` is a projection.  On its range `D=-1`; since `D=TY` and `Y` is
an involution, `T=-Y`.  Thus `(T-Y)P_zP_D=-2YP_zP_D`, whose norm is two on
every nonzero common carrier.  This proves `(TYC7)`.  The robust overlap
form in `(URR5)` gives the final asymptotic statement.

For the literal middle-index contact, prefix cancellation gives

```text
a_1d
 =s_1t_0(t_00+s_0t_00)
 =s_1t_000+s_1t_00
 =a_3+a_2,

db_2
 =(t_00+s_0t_00)s_00t_1
 =t_1+s_0t_1
 =b_0+b_1.
```

The ordinary composable-root commutator law therefore gives

```text
[C_7,D]=x_18(a_2+a_3),
[D,D_8]=x_73(b_0+b_1).
```

The factors in each displayed root subgroup commute, and characteristic
two makes every root element an involution.  Multiplication by `C_8` and
`D_7` cancels the old directions `a_2` and `b_1`, proving `(TYC8)`.  Finally

```text
t_1a_3s_000=t_1s_1(t_000s_000)=1,
b_0s_1=t_1s_1=1,
```

so neither ejected coefficient is zero and each has a one-sandwich inverse.
This proves `(TYC9)--(TYC10)`.  These identities use the literal roots from
`middle-index-marked-heisenberg-packet-is-whitehead-equivariant`; they do
not manufacture dual roots for the nine-pair spectator packet.  They hence
avoid that spectator typing error, while stopping short of a Hecke-source
mass estimate.
