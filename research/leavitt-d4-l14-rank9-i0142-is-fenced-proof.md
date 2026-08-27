---
rg: 2
id: leavitt-d4-l14-rank9-i0142-is-fenced-proof
kind: route
title: Eliminate all five branches of inverse class 0;142
target: leavitt-d4-l14-rank9-i0142-is-fenced
requires:
  - leavitt-d4-l14-seven-syllable-splitter
---

Use the representative

```text
face0=(A^-1,P^-1,Q^-1), face1=(Q,R^-1,B^-1),
T0=P, T1T2T3T4=C^-1, T5T6=R.
```

Its carriers and boundary are

```text
H^-1B0=E1^-1H^-1,
H^-1C0=A1^-1H^-1,
H^-1B1=E7^-1 H E6^-1 H,
K=A0^-1H^-1C1^-1H E5^-1H^-1E4^-1H
  E3^-1H^-1E2^-1H.
```

In branch I, `E1=1` makes the first equation `B0=1`.  The last carrier
equation then forces `H=1`, `d=vw`, and `p=(vw)^-1`; hence
`K=p^-1w^-1v^-1=1`.  Branch II similarly gives `d=v,p=v^-1` and
`K=1`.  In branch III, cyclic reduction of `H^-1B0H=z^-1_3` and factor
malnormality give `H=1,c=z^-1,pd=z`; the last equation gives `d=w`, and
`K=z^-1_3w_0w^-1_0z_3=1`.

For branches IV and V, moving the first carrier equation to one side gives a
word with copy pattern

```text
3,2,1,0,1,2,3,0,1,2,3.
```

Its 52 noncrossing partitions refine four maximal ones.  Substitution in
each maximal partition forces

```text
g10=g11=g12=g13=g3=1, H=f_2, f=g1g9.
```

The last carrier equation is then

```text
f^-1_2a_0=u^-1_0p^-1_1f_2a^-1_1u_0f_2.
```

Normal-form comparison forces `f=1`, and then `a=p=1`.  Thus `H=1`.
Branch IV has boundary `y_3y^-1_3=1`, while branch V has
`v_0v^-1_0=1`.  All five exhaustive branches therefore have identity
boundary.

