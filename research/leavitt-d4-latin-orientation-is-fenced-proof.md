---
rg: 2
id: leavitt-d4-latin-orientation-is-fenced-proof
kind: route
title: Convert projection equations to an order-sixteen packet and inspect the full word
target: leavitt-d4-latin-orientation-is-fenced
requires:
  - leavitt-d4-latin-triangle-reduction
---

Assume `E1=E2=E3=1` and `E0=h != 1` for the four projections in the Latin
reduction.  Put

```text
x=b^-1a,  w=a^-1d,  z=d^-1c,  y=c^-1b.
```

Then `xwzy=1`.  Direct substitution into `E3,E2,E1` gives successively

```text
x=w^2z,
z w z^-1=w^-3,
y=z^-2w,
z^4=w^12.                                                   (1)
```

Conjugating `w` by `z^4` gives `w^80=1`.  Since `z^4=w^12` commutes with
`z`, `(1)` also gives `w^48=1`; hence `w^16=1`.  Finally

```text
E0=x^2 w x w z=w^8.                                         (2)
```

Because `E0` is nontrivial, `w` has exact order sixteen.  It follows at once
from `(1)` that `x,w,z,y` are nontrivial: making any of `x,z,y` trivial would
make `z` commute with `w` and force `w^4=1`.  The same argument shows that

```text
xw=b^-1d,       wz (conjugate to c a^-1),
xwz=y^-1
```

are nontrivial.

After only the forced same-copy multiplications, the full boundary `(1)` of
the Latin reduction is

```text
a^-1_3 d^-1_2 c^-1_1 (b^-1a)_0 b_1 c_2 (d a^-1)_3
d^-1_2 c^-1_1 (b^-1d)_0 a_1 b_2 (c a^-1)_3
d^-1_2 c^-1_1 (b^-1c)_0 d_1 a_2 b_3.                       (3)
```

All five displayed bridge units in parentheses are nontrivial.  Adjacent
members of the cycle `a,b,c,d` cannot both be the identity because
`x,w,z,y` are nontrivial.  The two remaining opposite possibilities also
fail: `a=c=1` makes `z=w^-1`, while `b=d=1`, together with `x=w^2z`, makes
`z` a power of `w`; either contradicts the nontrivial conjugation in `(1)`.
Thus at most one of `a,b,c,d` is the identity.

If none is the identity, `(3)` is already a reduced word of length nineteen.
Deleting all occurrences of any one identity unit never makes two neighboring
copy indices equal in the displayed `3,2,1,0,1,2,3,...` pattern.  Hence `(3)`
still has length greater than one.  It cannot equal the one-copy word `h_j`.
The other target copies follow by cyclic relabeling.
