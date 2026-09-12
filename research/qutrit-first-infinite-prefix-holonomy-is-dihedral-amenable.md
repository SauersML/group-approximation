---
rg: 2
id: qutrit-first-infinite-prefix-holonomy-is-dihedral-amenable
kind: claim
title: The first infinite Leavitt qutrit holonomy is dihedral and residually finite
artifacts:
  - research/qutrit-infinite-dihedral-holonomy-proof.md
distinct_from:
  qutrit-first-mismatched-prefix-holonomy-is-d8: that consumes the one-sided inverse t0s0=1 and closes to a finite D8 packet; this uses two independent positive prefix letters and obtains a genuine infinite-order relative holonomy.
  qutrit-matched-prefix-router-family-is-one-finite-hnn-chart: that has only scalar pair ratios; this gives two non-scalar, noncommuting ratios between inequivalent rectangular prefix equivalences.
  leavitt-hyperlinear-branch-implies-thompson-v-hyperlinear: that warns that a full Thompson-V holonomy reaches an open hyperlinearity problem; this isolates the strictly smaller first infinite package and proves it amenable.
---

Use the simultaneous `h=J^2Z`-fixed basis from the D8 mismatch.
Choose a trivial `C` coordinate `i` and a coordinate `j` in the
nontrivial two-dimensional `C`-type killed by `h`. In normal
coordinates put

```text
X=x_(ij)(s_0),               Y=x_(ji)(s_1),             (QID1)
```

and conjugate them back by `P_h`. Both are legitimate relative prefix
holonomies: if `D` is the rectangular conjugator, then `XD` and `YD`
are two further invertible intertwiners from the `J` normal form to the
`h` normal form.

The roots `X,Y` are involutions, but their product has infinite order.
Indeed, in their active two-coordinate block,

```text
W=XY=[1+s_0s_1  s_0; s_1  1],
```

and the `(1,1)` entry of `W^n` contains the unique highest-degree
monomial `(s_0s_1)^n`. Hence

```text
<X,Y> isomorphic to D_infinity.                          (QID2)
```

The commutator `[X,Y]=W^2` carries nonconstant positive Leavitt words;
this holonomy cannot factor through any finite vertex packet.

Nevertheless its full qutrit atom action is still balanced. For
`v=X,Y`,

```text
C intersect vCv^(-1)=<h>,
p_(alpha',beta') v p_(alpha,beta) !=0
 iff 2alpha'+beta'=2alpha+beta,
||p_(alpha',beta') v p_(alpha,beta)||_2^2=1/27.         (QID3)
```

Thus both noncommuting mismatches have the same complete three-by-three
graph on every `h`-spectral fibre. Their infinite product creates
holonomy only on the multiplicity space; it does not orient one of the
three equal qutrit cells.

Let `K=GL_28(F_2)`. The dihedral subgroup meets `K` trivially and
centralizes `h`, so all displayed relations have the explicit cover

```text
K *_(<h>) (<h> times D_infinity)
       -> <K,X,Y> <= EL_28(L).                           (QID4)
```

The second vertex is amenable and the edge is finite, so the cover is
sofic and hyperlinear. In fact the concrete matrix subgroup is itself
residually finite. All of its entries lie in the positive free subalgebra

```text
B=F_2<s_0,s_1>.
```

Quotienting `B` by all words of length at least `N` gives finite rings
which separate its elements, and therefore separates every nonidentity
matrix in `<K,X,Y>`. Thus the actual subgroup, not only the cover, is
sofic and hyperlinear. Its finite quotient microstates keep all nine
qutrit character weights equal to `1/9`. This is a genuine infinite-order
seam but still has zero normalized-HS relator floor and no Hall trace
contradiction.

The theorem closes the first infinite package. To go further one must
consume a negative prefix letter in the same coefficient chart, couple
holonomies by a non-residually-finite relation, or pass to a prefix-table
subgroup at least as hard as the open Thompson-V hyperlinearity problem.
