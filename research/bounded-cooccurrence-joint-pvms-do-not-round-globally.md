---
rg: 2
id: bounded-cooccurrence-joint-pvms-do-not-round-globally
kind: claim
title: Bounded co-occurrence joint PVMs do not round to one global PVM
distinct_from:
  bounded-neighbor-pauli-needs-growing-equality-components: that bounds the dimension needed to realize arbitrary sparse signed pair tests; this gives zero local commutation defect but a constant global commutator and rounding defect.
  expander-edge-overlay-detects-simplex-exterior-square: that succeeds after Pauli labels are global affine-code sections; this countermodel uses arbitrary sparse supports and proves that the edge overlay cannot perform the preceding operator-to-section decoding.
---

ESTABLISHED.  Let `H` be any family of local joint-measurement contexts on
`N` distinguished binary coordinates.  Suppose the co-occurrence graph---two
coordinates are adjacent when some context contains both---has maximum degree
at most `Delta`.  For all `N >= 2(Delta^2+1)` there are reflections
`Q_x in M_2(C)` such that every context in `H` has a joint PVM, while

```text
E_(x,y)||Q_x Q_y-Q_y Q_x||_2^2
  >= 1/(Delta^2+1)^2.                                      (BCJ1)
```

Moreover every globally commuting reflection table `P_x` obeys

```text
E_x ||Q_x-P_x||_2^2 >= 1/(16(Delta^2+1)^2).                (BCJ2)
```

Thus even an exact fixed-arity, bounded-coordinate-incidence collection of
unrestricted joint-PVM tests admits a constant-dimensional contextual table a
constant average distance from every global PVM.  Spectral expansion of the
co-occurrence graph does not help: the construction works for every
bounded-degree graph, including the overlay in
`expander-edge-overlay-detects-simplex-exterior-square`.

The missing test must therefore be algebraic, not merely a higher-arity
jointness context.  It must prevent a nonidentity operator sector from being
supported on a sparse co-occurrence-independent set.  For affine simplex
coordinates the first perfect-complete local relation capable of doing this
has arity four, as recorded in
`four-local-parallelograms-are-minimal-simplex-operator-views`.

