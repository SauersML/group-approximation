---
rg: 2
id: depth-two-cousin-ut5-fusion-proof
kind: route
title: Fuse three UT4 centers and let S3 permute the complete payload chains
target: depth-two-cousin-loop-has-finite-ut5-fusion-model
requires:
  - outer-root-leavitt-table
  - leavitt-range-sum-fold-is-first-object-erasing-row
---

Prefix cancellation gives

```text
t_u s_u=A,                    t_v s_v=A,
```

and the active support identities remove the two intermediate copies of
`A`, proving `(DTL1)`.  Apply the ordinary adjacent-root commutator identity
from the inside out:

```text
[x_34(t_v),x_45(s_v)]=x_35(A),
[x_23(s_u),x_35(A)]=x_25(s_u),
[x_12(t_u),x_25(s_u)]=x_15(A).                         (1)
```

This proves `(DTL2)` with the literal shared occurrences.  A first mismatch
replaces one displayed coefficient by zero and proves each crossed-zero
variant.

For the finite model, let

```text
B=UT_5(F_2),
a=e_12(1),              b=e_23(1),
c=e_34(1),              d=e_45(1),
z=e_15(1).                                                (2)
```

Direct unitriangular multiplication gives

```text
[a,[b,[c,d]]]=z,              z^2=1,                   (3)
```

and `z` is central and nonidentity.  In `B^3`, denote the three central
copies by `z_a,z_b,z_c` and set

```text
N=<z_a z_b z_c>,
G_0=B^3/N.                                               (4)
```

The element in `(4)` is central of order two.  In the center quotient

```text
<z_a,z_b,z_c>/<z_a z_b z_c> ~= (C_2)^2,                (5)
```

each `z_r` remains nonidentity and

```text
z_b z_c=z_a.                                           (6)
```

The symmetric group permutes the three factors of `B^3`, preserves `N`, and
hence acts on `G_0`.  Form the finite semidirect product

```text
G=G_0 semidirect S_3.                                  (7)
```

Assign `J=z_a`, `C_0=z_b`, `C_1=z_c`.  Assign the four-arm nested payload
loop in each chart to the corresponding copy of the root chain `(2)--(3)`;
unused outer occurrences may be repeated or assigned identity according to
their crossed-zero role.  The two transpositions taking `a` to `b,c`
conjugate every generator of the first `B` copy to the matching generator of
the target copy, so all individual-arm Whitehead occurrence squares are
exact.  Equation `(6)` is the fold `(DTL3)`.

Finally take the left regular unitary representation of the finite group
`G`.  Every displayed word is exact, while `J=z_a` is nonidentity and hence
has a nonzero nontrivial spectral projection.  Zero prototype defect in this
model rules out any implication from the tested table to `(BAC1)`.
