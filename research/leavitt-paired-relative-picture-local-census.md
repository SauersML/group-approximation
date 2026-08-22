---
rg: 2
id: leavitt-paired-relative-picture-local-census
kind: claim
title: The paired length-six quotient has exactly two short torsion gates and no other coefficient region through degree four
distinct_from:
  leavitt-length-six-full-support-torsion-candidate: That constructs the equation and its paired kernel presentation; this classifies the local coefficient regions and symmetrized overlaps of that presentation.
artifacts:
  - research/leavitt-paired-relative-picture-local-census-proof.md
  - research/artifacts/verify-leavitt-paired-short-corner-relations.py
---

Put `H=G_0*G_1` and write the two relators of the degree-two kernel as

```text
R_0=h_0 z h_1 z h_2 z^(-1),
R_1=k_0 z k_1 z k_2 z^(-1),
```

where

```text
h_0=a_0b_1, h_1=c_0d_1, h_2=e_0,
k_0=a_1,    k_1=b_0c_1, k_2=d_0e_1.
```

Among cyclically formally reduced products of at most four oriented corner
labels, the only degree-two relations are `h_2^2=1` and `k_0^2=1`; there are
no degree-one or degree-three relations; and every degree-four relation
splits cyclically into two of those square relations.

In the symmetrized family of cyclic conjugates of `R_0^(+-1),R_1^(+-1)`, the
only common initial subwords longer than one syllable are the subwords of

```text
z h_2 z^(-1)       and       z^(-1) k_0 z.
```

Both length-three words are involutions.  Thus the paired presentation fails
the relative `C(6)` overlap test in exactly two places.  A curvature proof
must control chains of these two torsion overlaps; there are no other local
coefficient relations of degree at most four available to close a region.

