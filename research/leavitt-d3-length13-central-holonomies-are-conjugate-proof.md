---
rg: 2
id: leavitt-d3-length13-central-holonomies-are-conjugate-proof
kind: route
title: Retract the common carrier equation and cancel its cyclic endpoint products
target: leavitt-d3-length13-central-holonomies-are-conjugate
requires:
  - leavitt-d3-length13-five-seven-holonomy-template
---

Write the thirteen cyclic coefficient slots as `g0,...,g12`.  Let the source
central unit be `k` and impose the central-palindrome branch

```text
g4=k,       g3=g5^-1,       g2=g6^-1,
g1=g6^-1 g7^-1.                                          (1)
```

Then the source holonomy `C1^-1 D1` is conjugate to `k^-1`.  Let the target
central unit be `l` and impose

```text
g0=l^-1,                 g12=l^-1 g7 g6.                 (2)
```

Then the three-syllable target holonomy `C5 D7^-1` is conjugate to `l`.

Before using `(1)` or `(2)`, retract the common-carrier equality onto copies
0, 1, and 2.  If `H2=g0 g8 g10` is the copy-2 projection of the unary pivot,
the three equations are

```text
g8 g10 = g3 g5 g7 g9,
g11 = g8 g10,
H2 g9 H2^-1 g12
  = H2 (g4 g6) H2^-1 g11.                               (3)
```

Equations `(1)` and the first two lines of `(3)` give

```text
d:=g11=g7 g9,                 H2=l^-1 d.                 (4)
```

Substitute `(1)`, `(2)`, and `(4)` into the last line of `(3)`.  Its left
side reduces to `l^-1 d g6`, while its right side is
`l^-1 d k g6 d^-1 l d`.  Cancelling the common prefix gives

```text
1 = g6^-1 k g6 d^-1 l d,
g6^-1 k g6 = d^-1 l^-1 d.                               (5)
```

Thus `k^-1` is conjugate to `l`.  These are precisely the source and target
holonomies up to their already displayed conjugating prefixes.  They are
therefore conjugate inside the coefficient group.  Unequal-order transport
is impossible throughout this arbitrary-unit branch.
