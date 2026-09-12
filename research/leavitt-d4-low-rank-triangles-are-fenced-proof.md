---
rg: 2
id: leavitt-d4-low-rank-triangles-are-fenced-proof
kind: route
title: Add the rank-seven projection fence and the exotic rank-nine length fence
target: leavitt-d4-low-rank-triangles-are-fenced
requires:
  - leavitt-d4-rank8-orientations-are-fenced
  - leavitt-d4-latin-orientation-is-fenced
---

The two rank-seven orientations are global inverses.  For one, the carrier
boundary has projections

```text
K0=a d^-1 b^-1 c,   K1=b a^-1 c^-1 d,
K2=c b^-1 d^-1 a,   K3=d c^-1 a^-1 b.
```

Assume `K1=K2=K3=1`.  The first equation gives `d=cab^-1`; the second gives
`[a,c]=1`; and the third gives `[b,ca]=1`.  Consequently
`c^-1bc=aba^-1`, and

```text
K0=a b a^-1 c^-1b^-1c=1.
```

Thus three trivial projections force the fourth to be trivial.

At rank nine, the all-normal orientation is the Latin orientation already
fenced in the required claim, and the all-inverse orientation is equivalent.
The remaining orientation has triples

```text
(A,Q,P),       (B^-1,Q,R^-1),       (P^-1,R^-1,C).
```

Its carrier matches are `B1=B0`, `B2=C1`, and
`A2=H^-1C0^-1H`.  Exact free-product comparison successively forces

```text
g5=g6=g7=g8=g9=1,  g0=1, g4=g1,  g3=1.
```

Put `x=g1`, `y=g2`, and `p=yx`.  The coefficient boundary is

```text
x_2 p_1 y^-1_3 p_2 p^-1_1 x^-1_2
p^-1_1 x^-1_2 x_1 y_0.                                  (1)
```

If `x,y,p` are nontrivial, `(1)` is reduced of length ten.  If respectively
`x=1`, `y=1`, or `p=1`, direct reduction leaves at least four syllables in
distinct copies unless `x=y=1`; in that final case `(1)=1`.  Hence it is
never a nontrivial one-copy word.  Together with the rank-eight theorem this
exhausts every orientation of rank at most nine.
