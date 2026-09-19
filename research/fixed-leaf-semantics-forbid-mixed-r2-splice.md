---
rg: 2
id: fixed-leaf-semantics-forbid-mixed-r2-splice
kind: claim
title: Exact contextual semantics forbid every finite-leaf mixed-R2 splice
invalidates:
  - finite-leaf-multicell-splice-closes-mixed-r2
distinct_from:
  common-pivot-r2-output-transposition-is-unique: that fixes the input and pivot and classifies possible output transpositions; this also retains the second contextual Carmichael factor and shows that its input and output are forced before the mixed equation is imposed.
  mixed-r2-boundary-is-one-finite-mark-centralizer-commutator: that treats arbitrary contextual word gauges and gives an area obstruction only when their relative correction escapes; this is a fixed six-leaf semantic obstruction with no area estimate.
  bare-r5-a6-collision-does-not-synchronize-shared-labels: that gives a matrix representation countermodel to an energy inequality; this proves a group-element incompatibility for every exact transposition factorization of the second contextual three-cycle.
---

There is first a representation-free cancellation.  If unitaries
`x_0,x_1,y_1,r` obey the private and mixed equations

```text
y_1^* x_1 y_1=r,              y_1^* x_0 y_1=r,                 (FLS0)
```

then `x_0=x_1`.  Thus a literal relator diagram for the mixed equation,
together with the already literal private R2 diagram, is already a relator
diagram synchronizing the two contextual inputs.  It cannot be obtained as
a prior exact word identity between two distinct contextual leaf swaps.

The obstruction remains even if one tries to change the second private
factorization before imposing `(FLS0)`.  Let `i,j,p,q` be distinct letters
in a finite symmetric group and put

```text
r=(p q),       s_i=(i p),       s_j=(j p),       t_j=(j q),
c_j=s_j t_j.                                                    (FLS1)
```

Suppose `x` is a transposition which retains the second contextual
Carmichael factor with the common pivot:

```text
x x^r=c_j.                                                      (FLS2)
```

Then

```text
x=s_j,                    x^r=t_j.                              (FLS3)
```

Consequently the mixed R2 equation with the first contextual input is
impossible:

```text
(x^r)^(-1) s_i x^r != r.                                       (FLS4)
```

Indeed the two transpositions in `(FLS2)` must have supports meeting in one
point, and their union is the support `{j,p,q}` of `c_j`.  The support of
`x` is therefore either `{j,p}` or `{j,q}`.  These two choices give the two
opposite three-cycles; the orientation `c_j=s_jt_j` selects `x=s_j`, proving
`(FLS3)`.  But the supports `{j,q}` and `{i,p}` are disjoint, so `t_j`
centralizes `s_i`.  The left side of `(FLS4)` is therefore `s_i`, not `r`.

Thus no bounded diagram which only renames or factors the **same exact leaf
transpositions** can manufacture the required cross-chart R2 cell while
retaining both contextual Carmichael semantics.  Extra R2--R5 cells do not
alter `(FLS2)` as an equality of permutations.  A surviving proof of
`bleak-quick-adjacent-seam-retains-one-mixed-r2-cell` must instead prove a
genuine analytic collapse of the two contextual occurrences in every small
matrix model; it cannot be a finite `S_6` word splice whose exact permutation
values remain the two distinct adjacent-chart values.  In particular, the
phrase "bounded R1--R5 diagram" cannot mean a van Kampen filling of the
canonical mixed boundary: `(FLS0)` shows that boundary is nontrivial in `V`.
The only surviving reading is a matrix-dependent correction/exactification
whose output is merely `O(delta)`-close to the contextual word occurrences.
