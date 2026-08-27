---
rg: 2
id: leavitt-hyperlinear-via-amenable-amalgam-hs-repair
kind: route
title: Repair the two amenable-face amalgam and restrict its canonical microstates to the Leavitt core
target: binary-leavitt-unit-group-hyperlinear
requires:
  - leavitt-amenable-amalgam-canonical-hs-repair
  - leavitt-one-compressor-join-is-proper-amalgam-quotient
---

If the proposed repair existed, its tuples would give canonical hyperlinear
microstates of

```text
J=<L,tau,c>.
```

Hyperlinearity passes to subgroups, so restricting to
`L=EL_3(L_(F_2)(1,2))` would make `L` hyperlinear. The established Leavitt
rank/self-similarity equivalence identifies `L` with the binary Leavitt unit
group `Q`, proving the target.

This is exactly the tempting positive lane suggested by the two amenable
one-compressor faces. It is invalidated by
`leavitt-amalgam-microstates-have-unrepairable-kernel`: the canonical amalgam
trace and quotient trace differ by one on every nontrivial killed kernel word,
so an `o(1)`-HS repair cannot even satisfy one such fixed relation.
