---
rg: 2
id: private-d8-cube-has-one-common-source
kind: claim
title: A finite cube of private dihedral packets has one common source and orthogonal context ranges
distinct_from:
  dihedral-spin-packet-supplies-common-partial-swap: that extracts one partial swap from one marked D8 packet; this tensors finitely many private copies and compresses every coordinate swap to the same bottom vertex of the role cube.
  common-source-partial-isometries-decode-one-game-state: that proves the semantic game decoder once a common initial projection is given; this supplies that projection kinematically but does not compile the context observables on it.
  common-source-orthogonal-partial-swap-star-compiler: that requires the literal swap words themselves to be Julia swaps with controlled complementary blocks; the coordinate reflections here contain many additional cube edges and only their compressed blocks have the common-source geometry.
  tensor-context-types-classicalize-common-source: that proves the obstruction created when selected context labels are also tensorized; this records the positive common-source half of the audit.
---

Let `K_c` be finitely many finite packets.  In each packet fix a central
selected-type projection `q_c`, a role involution `z_c`, and a reflection
`j_c` such that on `q_c` the pair `(z_c,j_c)` is the marked two-dimensional
`D_8` spin:

```text
j_c p_(c,-) j_c=p_(c,+),
p_(c,+)p_(c,-)=0,
p_(c,+)+p_(c,-)=q_c,                                  (PDC1)
```

where `p_(c,+),p_(c,-)` are the two role halves of `q_c`.  Put

```text
K=product_c K_c,
Q=product_c p_(c,-).                                  (PDC2)
```

Inside every exact representation of `K`, the compressed coordinate words

```text
S_c=j_c Q                                               (PDC3)
```

are partial isometries with

```text
S_c^*S_c=Q,
S_cS_c^*=p_(c,+) product_(d!=c) p_(d,-),
(S_cS_c^*)(S_dS_d^*)=0                (c!=d).          (PDC4)
```

Thus all contexts have literally the same initial projection and pairwise
orthogonal ranges.  If every selected spin half is nonzero, the regular
trace of the finite direct product gives

```text
tau_K(Q)=product_c tau_(K_c)(p_(c,-))>0.               (PDC5)
```

The number of contexts is fixed, so `(PDC5)` is a fixed positive constant,
however small.  Exactification of the complete multiplication table of the
fixed finite group `K` gives the same conclusion in normalized
Hilbert--Schmidt microstates with a dimension-independent modulus.

This closes the purely geometric proposal: private tensorized D8 packets
really do provide the common initial projection allowed by
`common-source-partial-isometries-decode-one-game-state`.  It does **not**
promote selected context truth tables to that source.  If the whole selected
context packets are tensorized as well, their pulled-back observables become
jointly commuting and the obstruction in
`tensor-context-types-classicalize-common-source` applies.

