---
rg: 2
id: atlas-second-core-rectangle-coupling-recreates-collision-proof
kind: route
title: Compute the two GL3 blocks and evaluate collision after canonical A8 coupling
target: atlas-second-core-rectangle-coupling-recreates-collision
requires:
  - atlas-s576-carrier-completes-first-core-k22
  - atlas-a4-aligned-component-generation-ladder
---

Let `R` be the frozen inner alignment and write the four raw small-component
labels as `h0,h1,a,a^-1`, with `h0,h1` involutions.  Exact `F2` matrix
arithmetic gives

```text
ord(a^-1 R h0 R^-1)=ord(h0 R a^-1 R^-1)=3,
ord(h1 R a R^-1)=ord(a R h1 R^-1)=3.              (RECT-1)
```

These labels generate a second subgroup `L_2~=GL3(F2)` of order 168.  If
`L_1` is the first rectangle group used in the 4032-point carrier, then

```text
|L_1|=|L_2|=168,       |L_1 intersect L_2|=6,
<L_1,L_2>=A8,          |A8|=20160.                 (RECT-2)
```

Thus the isolated second rectangle is completely finite.  The canonical
coupling is an `A8` vertex, and its index over each rectangle group is 120.

Now insert the exact collision coefficient `c`.  The same computation shows

```text
c in L_2,       |<r,u,b,c>|=48,                    (RECT-3)
```

where `<r,u,b>~=S4` is the overlap from the first-rectangle carrier.  Although
`c` centralizes this `S4`, it is not an independent central factor after the
second rectangle is attached.  With `t=y^-1` and `s=b y`, direct evaluation
of the collision word gives

```text
t c s c t^-1 c s t c = c != 1.                    (RECT-4)
```

In particular the tempting regular gluing of `H_576` to canonical `A8` over
the order-48 overlap would have perfectly matching multiplicities on 20160
points (`35*576=20160`), but fails exactly one required equation: `(RECT-4)`.
The unresolved global problem is therefore not either rectangle separately;
it is a noncanonical coupling of the two finite `GL3` blocks that simultaneously
kills the collision word without collapsing their marked subgroups.

The preceding 4032-point carrier has an even sharper obstruction.  There `c`
is central in `L_1`, hence `ord(yc)=6` and `<b,y,c>` has order 12.  In the
canonical second rectangle,

```text
ord(yc)=3,       ord(byc)=4,       |<b,y,c>|=24.          (RECT-5)
```

Orders of a fixed marked word cannot change inside an injective overgroup, so
these two marked finite vertices admit no injective amalgam.  Any global
countercarrier must retune the first rectangle so that `c` is already
noncentral; merely enlarging the 4032-point rung cannot work.
