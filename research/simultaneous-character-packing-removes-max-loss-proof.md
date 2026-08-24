---
rg: 2
id: simultaneous-character-packing-removes-max-loss-proof
kind: route
title: Sum all transported projection traces before applying the marked-sector capacity bound
target: simultaneous-character-packing-removes-max-loss
requires:
  - finite-subgroup-type-exclusion-is-already-nonhyperlinearity
---

Conjugation preserves normalized trace, so

```text
tr(p_(i,r))=tr(e_i).                                     (SCP-P1)
```

Pairwise orthogonality and `p_(i,r)<=Q_-` give, at every exactified matrix
coordinate,

```text
K sum_i tr(e_i)
  =sum_(i,r) tr(p_(i,r))
  =tr(sum_(i,r) p_(i,r))
  <=tr(Q_-).                                             (SCP-P2)
```

For approximate packets, every character projection is a fixed finite
group-algebra polynomial and every conjugator is a fixed word.  Flexible
exactification of the fixed packets and word telescoping change `(SCP-P2)`
by `o(1)`.  Combining it with `(SCP1)` and taking limits gives

```text
K beta a<=h,
```

which is `(SCP3)`.  If the strict reverse inequality holds, canonical
matrix microstates cannot exist.  The canonical trace of a hyperlinear group
has such microstates, so the group is nonhyperlinear.

For packing within a single type, `(SCP1)` gives some `i` with

```text
tr(e_i)>=(beta/M)tr(Q_0)-o(1).                           (SCP-P3)
```

Apply the same calculation to the `K` conjugates of that `e_i`.  Substituting
`a=1/4` and `h=1/2` gives `(SCP4)` and `(SCP5)`.
