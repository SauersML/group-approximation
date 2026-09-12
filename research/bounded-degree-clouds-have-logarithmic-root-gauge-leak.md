---
rg: 2
id: bounded-degree-clouds-have-logarithmic-root-gauge-leak
kind: claim
title: Bounded-degree equality clouds have a logarithmic rooted gauge leak
distinct_from:
  regular-tree-consistency-has-vanishing-spectral-gap: that cuts a finite tree and pays one bad edge in average; this applies to every bounded-degree cloud, including expanders, and makes the maximum defect of every edge tend to zero.
  equality-synchronized-lifts-create-two-pair-contours: that is a word-placement obstruction caused by repeating a mixed pair; this is an analytic same-basis obstruction with only one distinguished mixed port.
  rooted-normalized-sum-linear-pcpp-needs-sqrt-n-norm: that is a scalar linear checker-norm obstruction; this uses exact reflection packets and a slowly varying noncommutative conjugation gauge.
---

Fix `Delta>=2`.  For every sufficiently large connected graph `C` of maximum
degree at most `Delta`, every distinguished vertex `o`, and `Q=|V(C)|`, there
are exact two-dimensional reflections `U_v` such that

```text
max_(uv in E(C)) ||U_u-U_v||_2 <= C_Delta/log Q,             (BRG1)
||U_o-Z||_2=sqrt(2),                                        (BRG2)
U_v=Z for all but O_Delta(Q^(1/4)) vertices.                 (BRG3)
```

Consequently no dimension-independent modulus can infer closeness of a
designated port to the bulk PVM from bounded-degree occurrence-equality
defects, even if **every** edge defect rather than their average is used.

The escape is coherent at the local-context level.  If every cloud vertex
carries one copy of an exact two-dimensional reflection packet and local predicates
are invariant under simultaneous unitary conjugacy, conjugate the entire
packet at vertex `v` by the same slowly varying rotation.  Every local
predicate remains exact and every overlap defect obeys `(BRG1)`, while the
root packet stays a fixed global gauge away from almost every other packet.

Thus dense BLR followed by bounded-degree equality-cloud reduction cannot
feed one private mixed port with uniform normalized-HS constants.  A surviving
same-basis compiler must give the selected ports positive test weight/effective
degree, place them directly in one noncontextual code packet, or use an actor
whose spectral inequality controls the root without a bounded-degree cloud.
