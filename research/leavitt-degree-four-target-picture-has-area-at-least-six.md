---
rg: 2
id: leavitt-degree-four-target-picture-has-area-at-least-six
kind: claim
title: Any revised degree-four KL picture with one-copy boundary has at least six relator vertices
artifacts:
  - research/leavitt-degree-four-target-picture-has-area-at-least-six-proof.md
  - research/artifacts/search-leavitt-degree4-relative-pictures.py
distinct_from:
  degree-four-kl-source-face-retraction: that gives an abstract packet countermodel to a four-cell source-face argument; this census uses exact equality in four full Leavitt coefficient copies.
  leavitt-three-gate-kernel-picture-has-area-at-least-six: that concerns the earlier cubic three-gate presentation; the revised degree-four presentation has two monovalent and two trivalent Reidemeister--Schreier relators.
---

For the revised word

```text
W'=r t e t a t^(-1)c t^2 b t^(-1)d t p t,
b=r^2 a r^(-2),                 d=p^2 c p^(-2),
```

there is no connected relative picture of area two or four whose inner
coefficient regions are trivial and whose outer boundary is any nonidentity
element lying wholly in one coefficient copy.  In particular this excludes a
boundary conjugate, by a corner rotation, to

```text
[c_0,d_0]=x_15(s_0^2)_0
```

or its inverse.  Odd areas are impossible by stable-letter sign balance.
Consequently any coefficient-killing picture, including a target-commutator
picture, has at least six relator vertices.

The coefficient tests are exact in the faithful twenty-leaf Bergman chart of
`EL_20(L_(F_2)(1,2))`; no finite quotient or truncation is used.
