---
rg: 2
id: source-affine-safety-profile-counterexample-proof
kind: route
title: Solve the three odd-parity rows on the affine plane and expose a forced Fano line
target: source-affine-safety-does-not-imply-rstar-profile-compatibility
requires:
  - rstar-fano-ghost-affine-hull-criterion
  - rstar-core-character-profiles-induce-an-exact-affine-cover
---

Direct substitution gives a witness for every visible triple; in lexicographic
order on `(p,q,r)` one may take `(a,b,c,d)` to be

```text
000 -> 0110      001 -> 0101
010 -> 1111      011 -> 1100
100 -> 0011      101 -> 1111
110 -> 0101      111 -> 0110.                           (ASC4)
```

Every displayed row has odd parity and is different from `1000`, proving
that the visible projection is `F_2^3`.

Now restrict to `p+q=1`.  Odd parity in the first row gives `a=b`.  If
`(p,q)=(0,1)`, the ghost exclusion in that row forces `a=b=1`.  If
`(p,q)=(1,0)`, the second row excludes `a=1` when `r=0`, while the third row
excludes `a=0` when `r=1`.  The four witnesses are therefore forced, and
the first-row values are, respectively,

```text
1011, 1011, 0100, 0111.                                (ASC5)
```

The three distinct values translate to `011,100,111`; the first two xor to
the third.  The first prerequisite says this is not cap-supported.  By the
second prerequisite, no induced affine-cover piece contains all of `S`.

