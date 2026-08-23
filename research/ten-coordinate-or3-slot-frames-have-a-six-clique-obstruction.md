---
rg: 2
id: ten-coordinate-or3-slot-frames-have-a-six-clique-obstruction
kind: claim
title: Six pairwise co-occurring variables obstruct every ten-coordinate OR3 root-slot frame
distinct_from:
  edgeful-or3-balanced-private-plane-packet: that constructs one local ten-coordinate packet with three disjoint private planes; this proves that those planes cannot be synchronized through one root skeleton on all finite clause incidences.
  coherent-balanced-context-permutations-would-give-a-ce-trace: that excludes a globally coherent family of complete context permutations using the no-CE source trace; this is a finite rank obstruction involving only the three deleted root planes, and already applies to a classically satisfiable six-variable formula.
  packet-retraction-evaluates-hecke-collision-atlas: that rules out a completed atlas whenever the ambient group retracts onto the finite packet; this rules out the literal root-slot matching required before any off-diagonal coefficient or retraction question arises.
---

**ESTABLISHED.**  In the ten-coordinate packet of
`edgeful-or3-balanced-private-plane-packet`, let `R_a,R_b,R_c` denote the
root-diagonal parts of the three conjugated logical marginals.  Their kernel
projections

```text
K_j=1-R_j^2,                 j in {a,b,c},               (TSO1)
```

have rank two in the ten-dimensional packet corner and are pairwise
orthogonal.  This remains true after common amplification and after
conjugating the whole clause packet by an arbitrary slot frame.

Consequently, suppose a coefficient compiler literally aligns the
root-diagonal part of every occurrence of a global variable `v` with one
common root skeleton `R_v`.  Put `K_v=1-R_v^2`.  Whenever distinct variables
`v,w` occur in one clause,

```text
K_v K_w=0,                    tr(K_v)=tr(K_w)=1/5.        (TSO2)
```

Take six variables and include an OR3 clause on every three-element subset.
This positive formula is classically satisfiable (set every variable to
one), but every pair of variables co-occurs.  Thus `(TSO2)` would give six
pairwise orthogonal projections of normalized trace `1/5`, whose sum has
trace `6/5`.  This is impossible.  Therefore the ten-coordinate packet
cannot furnish the root-skeleton/slot-frame part of a uniform signed-3SAT
coefficient-link compiler.

There is also a dimension-free robust form.  For any six projections
`P_1,...,P_6` with normalized trace `1/5`,

```text
sum_(i<j) ||P_i P_j||_2^2 >= 3/25,                       (TSO3)
max_(i<j) ||P_i P_j||_2^2 >= 1/125.                      (TSO4)
```

Hence amplification cannot make the six-clique obstruction disappear.  An
approximate implementation which keeps the rank-`1/5` deleted planes must
pay a fixed overlap before any private-pivot or packet-term bijection is
examined.

This does **not** refute `edgeful-or3-coefficient-link-compiler`, because
that claim also permits the zero-root-diagonal four-cap packet.  It refutes
the proposed ten-coordinate branch as a universal compiler and moves the
live finite search entirely to the four-cap/noncentral-sector branch (or to
a packet with a number of root slots growing with the source incidence).

