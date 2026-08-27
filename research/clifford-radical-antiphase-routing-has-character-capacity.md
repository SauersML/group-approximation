---
rg: 2
id: clifford-radical-antiphase-routing-has-character-capacity
kind: claim
title: Multi-axis Clifford antiphase routing still has radical-character capacity
artifacts:
  - experiments/v4_pairwise_antiphase_capacity.py
distinct_from:
  affine-source-charts-have-a-disjoint-tag-packing-ceiling: that packs disjoint characters of one common finite tag group; this permits a separate Pauli comparison axis on every edge and derives the same capacity from simultaneous Clifford-frame compatibility.
  one-axis-pairwise-antiphase-routing-fails-on-triangles: that rules out one reused local axis already on three branches; this allows the full Weyl axis space at each branch and gives the sharp bound N less-than-or-equal-to 2^r.
  pairwise-antiphase-covariance-controls-cross-gram: that proves overlap payment once pairwise antiphase comparisons are supplied; this bounds how many such comparisons a Clifford/radical word atlas can supply coherently.
---

Let `D=F_2^r` be a radical word space.  On the failure sector of branch `i`,
the words of `D` act by a character `chi_i in D^*`.  On its satisfying
sector, assume the same words form a Weyl/Pauli frame, and one branch
transporter identifies that complete frame with a common target Weyl frame
through a Clifford automorphism and Pauli sign gauge.

After expressing every local frame in the common target coordinates, there
is one effective character

```text
a_i in D^*                                                (CRAC1)
```

such that the difference between the failure-source phase and the transported
target phase on axis `w in D` is `a_i(w)`.  Therefore a pair-specific target
axis `w_ij` has opposite source phases on branches `i,j` only if

```text
(a_i+a_j)(w_ij)=1.                                      (CRAC2)
```

Such an axis exists exactly when `a_i!=a_j`.  A complete pairwise antiphase
router on `N` branches consequently requires

```text
N<=|D^*|=2^r.                                           (CRAC3)
```

This remains true although every edge may use a different packet word and
every vertex may use an arbitrary Clifford change of frame.

For the synchronized V4 atlas, the four radical atoms have failure
multiplicities

```text
2,1,1,1,                                                 (CRAC4)
```

by `(VOF2)`.  Thus its five failure-atom occurrences would require five
pairwise distinct effective characters in a two-dimensional radical dual,
which has only four.  The proposed pairwise Clifford router is impossible
already for one V4 batch.

Nor does tensoring with `t` dummy radical coordinates repair it.  Splitting
the source into the enlarged radical atoms multiplies the number of failure
occurrences and the number of available effective characters by the same
factor:

```text
5*2^t > 4*2^t.                                          (CRAC5)
```

Hence the V4 five-fourths surplus is exactly the obstruction to a pure
Clifford-character antiphase atlas.  A surviving pairwise router must use a
non-character multiplicity decoder, a contextual cross-copy operation, or a
genuinely non-Weyl coefficient system; adding axes or affine dummy clocks is
not enough.
