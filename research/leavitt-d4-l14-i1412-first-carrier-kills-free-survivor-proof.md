---
rg: 2
id: leavitt-d4-l14-i1412-first-carrier-kills-free-survivor-proof
kind: route
title: Substitute the free third-carrier solution in the raw first carrier word
target: leavitt-d4-l14-i1412-first-carrier-kills-free-survivor
requires:
  - leavitt-d4-l14-i1412-has-free-rank-three-one-copy-survivor
---

Use the exact specialization from `(I14-2)`:

```text
g1=P, g2=Q, g4=Q^-1, g5=R, g6=1, g7=R^-1, g8=1,
g9=g10=g11=g12=Q^-1, g13=P^-1.                       (I14-6)
```

Now read the 31 coefficient syllables of the first inverse carrier equation
from `RAW_S` in `enumerate-l14-i1412-eq1-maximal.py`, retaining their copy
colors.  Under `(I14-6)`, positions `0..12` reduce as follows.  The copy-two
terms `Q,R,R^-1,Q^-1` cancel, the copy-one terms `Q,Q^-1` cancel, and the
two surviving copy-three terms multiply to

```text
Q_3 (P^-1 Q)_3=(Q P^-1 Q)_3.                          (I14-7)
```

In positions `13..29`, the same `R,R^-1`, `Q,Q^-1`, `uv=1`, and `ep=1`
pairs cancel completely in their respective copies.  Position `30` is

```text
(g10 g2 g4)_3=Q^-1_3.                                 (I14-8)
```

Combining `(I14-7)` and `(I14-8)` gives the full first-carrier relator

```text
(Q P^-1 Q)_3 Q^-1_3=(Q P^-1)_3.                       (I14-9)
```

But `(I14-5)` computed the outer boundary of the third-carrier half-picture
as the same word `K=(QP^-1)_3`.  The first carrier equation requires
`(I14-9)=1`; hence it requires `K=1`.  This obstruction precedes any Peiffer
or global coefficient-injectivity issue: the two carrier equations already
identify the proposed mark with a defining relator.

