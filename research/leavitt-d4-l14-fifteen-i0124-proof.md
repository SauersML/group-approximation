---
rg: 2
id: leavitt-d4-l14-fifteen-i0124-proof
kind: route
title: Collapse both inverse fifteen-winner 0;124 branches
target: leavitt-d4-l14-fifteen-i0124-is-fenced
requires:
  - leavitt-d4-l14-fifteen-winner-profile-has-five-classes
---

Use the inverse triangle orientations

```text
face0=(id1^-1,id0^-1,id2^-1),
face1=(id2,id4^-1,id3^-1)
```

and the valence-seven assignment

```text
T0=id0, T1 T2=id5^-1, T3 T4 T5 T6=id4.
```

Literal multiplication of the raw corners gives

```text
R0=H^-1 B0 H E1,
R2=H^-1 C0 H A1,
R4=H^-1 B1 H^-1 E4 H^-1 E5 H E6 H^-1 E7,
K =A0^-1 H^-1 C1^-1 H E3^-1 H^-1 E2^-1 H.
```

The twelve copy retractions of the three carriers reduce exactly to free
coordinates `q,r,s,t,u`:

```text
g0=g8=1; g1=t; g2=u; g3=s^-1; g4=t^-1s^-1;
g5=s; g6=st u^-1; g7=t^-1s^-1;
g9=q; g10=r; g11=q^-1; g12=r^-1; g13=s.
```

The full common carrier then is

```text
u_3 (s^-1)_2 (t^-1s^-1)_3 s_2 (st u^-1)_3.
```

Its two maximal noncrossing cancellation branches are exhaustive:

```text
I:  s=1;
II: t=s^-1.
```

Substitution into the literal raw boundary makes `K` freely reduce to the
empty word in both branches.  This conclusion precedes, and is independent
of, the other two carrier identities; hence it fences the whole cyclic class.
