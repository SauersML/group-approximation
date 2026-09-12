---
rg: 2
id: stw83-arbitrary-cycle-synchronizer-proof
kind: route
title: Order cyclic edges first and retain the old synchronizers through desingularization
target: stw83-arbitrary-cycle-synchronizer-dimension-one
requires:
  - stw83-finite-cycle-synchronizer-dimension-one
---

Take a Drinen--Tomforde desingularization `F` of `E`.  At each cyclic infinite
emitter enumerate first all emitted edges which themselves belong to a cycle.
There are only finitely many such edges in total by the finite cyclic-edge
hypothesis.

The Drinen--Tomforde path correspondence collapses each added tail segment and
sends every cycle of `F` to a cycle of `E`; every old cycle lifts.  Since the
cyclic emitted edges were placed first, all lifted cycles use only the old
finite cyclic subgraph and finitely many initial tail vertices.  Thus `F` again
has a finite cyclic nucleus.  A sink tail creates no cycle, and a later
redistributed edge cannot create one: collapsing such a cycle would make the
original edge cyclic.

The old finite set `H` is still a synchronizer.  Every lifted cycle reaches
every `h in H` by lifting the corresponding old path.  If an old noncyclic
vertex `v` is reached by a lifted cycle, collapse the path to see that an old
cycle reaches `v`; an old hub reaches `v`, and that path lifts.  A tail based
at a noncyclic singular vertex is handled the same way.  A tail based at a
cyclic infinite emitter is reached from a hub by Condition 3, including beyond
the finite prefix containing the lifted cycles.  Hence every noncyclic vertex
of `F` reached by a cycle is reached by an old hub.

Drinen--Tomforde, Lemma 2.7(b), preserves Condition (K), and `F` is row-finite.
Thus `stw83-finite-cycle-synchronizer-dimension-one` gives

```text
dim_nuc(C*(F)) <= 1.
```

Their Theorem 2.11 identifies `C*(E)` with a full hereditary corner of
`C*(F)`.  Nuclear dimension is invariant under full hereditary corners, giving
the same bound for `C*(E)`.
