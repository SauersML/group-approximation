---
rg: 2
id: bare-r5-a6-collision-does-not-synchronize-shared-labels
kind: claim
title: The bare R5 A6 collision does not synchronize the two shared A5 labels
invalidates:
  - bare-r5-collision-closes-pointwise-a5-seam
distinct_from:
  a5-a4-overlap-has-two-seam-charges: that identifies two representation-ring seam directions when adjacent A5 restrictions agree on A4; this gives an exact A6 model showing that even the missing nonshared cross-pair relation is blind to a permutation of the shared contextual labels.
  thompson-v-r5-a6-seam-pointwise-synchronization: that remains an existential claim about contextual conjugates extracted coherently from one Bleak--Quick approximate model; this refutes only the proposed local inference from two A5 chart energies plus the single R5 collision energy.
  affine-clone-model-defeats-pure-thompson-prefix-error-spreading: that is an unbounded prefix-clone private-gauge model; this is the minimal five-dimensional alternating-group obstruction on one adjacent seam.
---

Let `p,q,1,2,3,4` be six letters and put

```text
c_i=(i p q) in A6,                         1<=i<=4.
```

On the five-dimensional standard summand of the permutation representation
of `A6`, consider the adjacent contextual Carmichael charts

```text
X=(X_1,X_2,X_3)=(c_1,c_2,c_3),
Y=(Y_1,Y_2,Y_4)=(c_2,c_1,c_4).                    (BRS1)
```

Every generator in either chart has order three and every within-chart pair
product has order two.  The nonshared pair also has order two:

```text
(X_3Y_4)^2=(c_3c_4)^2=1.                         (BRS2)
```

Indeed `c_i c_j=(i p)(j q)` for `i!=j`.  Thus `(BRS2)` is exactly the
disjoint-transposition commutator supplied by a conjugate of the
Bleak--Quick R5 relation

```text
[(000 010),(10 110)]=1.
```

Nevertheless the two shared contextual occurrences are swapped rather than
synchronized.  With normalized Hilbert--Schmidt norm on the standard
five-dimensional summand,

```text
||X_1-Y_1||_2^2=||X_2-Y_2||_2^2=6/5.             (BRS3)
```

Consequently there is no dimension-free inequality bounding the shared
pointwise mismatch by the sum of the two local A5 Carmichael defects and the
single nonshared R5/A6 collision defect.  Any proof of pointwise Thompson
seam synchronization must retain an additional label-sensitive anchor, for
example an occurrence comparison transported by R2 or the coarse split
identity R3; the R5 collision alone cannot kill the label-permutation gauge.
