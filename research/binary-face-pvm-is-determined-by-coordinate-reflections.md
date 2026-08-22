---
rg: 2
id: binary-face-pvm-is-determined-by-coordinate-reflections
kind: claim
title: A binary face PVM has no gauge beyond its coordinate reflections
distinct_from:
  finite-groupoid-diagonals-have-only-classical-gluing: that concerns groupoid realizations of whole BCS diagrams; this is the elementary operator identity inside one binary joint measurement.
  bounded-cooccurrence-joint-pvms-do-not-round-globally: that allows noncommuting coordinates across contexts; this proves uniqueness after the coordinate marginals are fixed within a face.
---

Let `(P_a)_(a in {0,1}^T)` be a joint PVM and define its binary coordinate
reflections

```text
Q_i=sum_a (-1)^(a_i) P_a,       i in T.                   (BFP1)
```

Then the `Q_i` commute and every atom is recovered exactly by

```text
P_a=prod_(i in T) (I+(-1)^(a_i)Q_i)/2.                    (BFP2)
```

Thus two binary face PVMs with the same coordinate reflections are equal.
If the face is supported on a local binary linear code, its parity relations
are exactly the corresponding products of the `Q_i`.

Because face width is bounded, `(BFP2)` is also uniformly Lipschitz: replacing
all coordinate reflections by `delta`-close commuting reflections changes
each atom by at most `|T| delta/2` in normalized HS norm, by telescoping.
There is therefore no independent face-unitary or multiplicity gauge to pin;
the only global difficulty is rounding the shared coordinate reflections to
one commuting code action.
