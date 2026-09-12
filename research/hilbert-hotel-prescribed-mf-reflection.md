---
rg: 2
id: hilbert-hotel-prescribed-mf-reflection
kind: claim
title: Hilbert-hotel absorption realizes every MF group as a prescribed visible quotient
distinct_from:
  full-mf-radical-absorber: that is the abstract quotient formula; this is its concrete realization with the Hilbert-hotel group and records the exact radical, finiteness, and C-star consequences.
artifacts:
  - research/hilbert-hotel-prescribed-mf-reflection-proof.md
---

Let

```text
H = EL_16(L_(F_2)(1,2))
```

and let `B` be any countable MF group.  Then

```text
Rad_MF(H x B) = H x {1},
(H x B)/Rad_MF(H x B) ~= B.                      (P1)
```

Thus every countable MF group occurs as the exact universal MF-visible
quotient of a non-MF group.  If `B` is finitely generated, the realizing
group is finitely generated.  Using the finitely presented Hilbert-hotel
cover in place of `H`, every finitely presented MF group is the exact
universal MF-visible quotient of a finitely presented non-MF group.

At the reduced C-star level the visible quotient disappears completely:

```text
C*_r(H x B)
```

has no nonzero MF image.  Hence the group-level MF reflection can be
prescribed arbitrarily while the reduced group C-star MF reflection remains
zero.
