---
rg: 2
id: leavitt-all-countable-central-covers-are-nonsofic
kind: claim
title: Every countable central extension of the binary Leavitt unit group is nonsofic
distinct_from:
  openai-leavitt-unit-nonsofic: that proves only that the binary Leavitt unit group itself is nonsofic; this persists through every countable central extension and therefore cannot be obtained from quotient closure of soficity.
  universal-leavitt-el4-nonsofic: that is the kernel-checked nonsoficity theorem for one concrete elementary group; this applies the universal-cover form of the Kazhdan infranormal obstruction to every countable central cover of that group.
  thom-central-corner-criterion: that is a positive permanence theorem saying hyperlinearity descends through central quotients; this is a negative soficity theorem special to the binary Leavitt compression configuration.
artifacts:
  - notes/NOTEPAD.md
  - notes/EXPLICIT_LEAVITT_ATLAS.md
---

Let

```text
L = L_(F_2)(1,2),            Q = EL_4(L) = L^x.
```

If

```text
1 -> Z -> E -> Q -> 1
```

is any central extension with `E` countable, then `E` is nonsofic.

This is not an assertion that soficity descends through arbitrary central
quotients. It is a theorem about this particular quotient. The one-sided
Leavitt compression configuration lifts through every central extension:
universal central extensions of both the ambient elementary group and its
compressed core have property `(T)`, perfectness removes the central errors in
the lifted commutation relations, and Kun--Thom centralizer normalization then
reproduces the original nonsoficity contradiction in `E`.

Consequently every central quotient of `St_n(L)` which still maps onto `Q` is
nonsofic, and no sofic image of the universal Leavitt atlas can have merely
central kernel while remaining nontrivial on either atlas chart.
