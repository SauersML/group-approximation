---
rg: 2
id: atlas-o8p2-carrier-a8-classes-and-absorption
kind: claim
title: The O8+(2) carrier fork has one orthogonal class, one natural class, and two affine complement classes locally
artifacts:
  - experiments/atlas_a8_2six_complement_classes.py
  - experiments/atlas-a8-2six-complement-classes.json
distinct_from:
  atlas-o8p2-a8-marked-carrier-fork: that identifies the nine maximal carriers by order; this classifies A8 subgroups inside each carrier type and says which existing packet theorem applies.
  atlas-a4-sp6-packet-collision-screen: that screens the orthogonal class inside one S6(2); this transports its scope to the O8+(2) carrier decomposition without screening cross-carrier cells.
---

Let `A~=A8` lie in one of the three maximal-carrier types of `G=O8+(2)`.
The local subgroup classification is as follows.

1. In `S6(2)=Sp6(2)`, every `A8` belongs to the single orthogonal class and
   is the derived subgroup of `S8=O6+(2):2`; its carrier normalizer has order
   40320.  Hence any marked pair lying in one common `S6(2)` carrier is
   already excluded by `atlas-a4-sp6-packet-collision-screen`.
2. In `A9`, every `A8` is a natural point stabilizer, one carrier class with
   normalizer `A8`.  Hence any pair lying in one common `A9` carrier is
   excluded by `atlas-natural-a8-supports-collapse-before-collision`.
3. In the split carrier `V:A8=2^6:A8`, where `V` is the six-dimensional
   orthogonal module, every `A8` is a complement to `V`.  There are exactly
   two carrier-conjugacy classes of complements.  Both are self-normalizing,
   and their affine degree-64 orbit profiles are respectively

   ```text
   28+35       and       8+56.                       (O8L1)
   ```

The last statement is exact `ComplementClassesRepresentatives` arithmetic.
Indeed `A intersect V` is normal in simple `A`, hence trivial, and the image
in the quotient `A8` has full order; therefore no non-complement `A8` was
missed.

For every `A8<G`, its ambient centralizer is trivial.  If an element
centralizes `A`, put `<A,c>` in a maximal subgroup.  The carrier fork forces
that maximal to have one of the three types above, and the displayed local
normalizers (or the natural point action) give trivial centralizer there.
Consequently

```text
N_G(A)/A embeds in Out(A8)=C2,
so |N_G(A)| is 20160 or 40320.                       (O8L2)
```

Thus the already established theorems remove the same-`S6(2)` and same-`A9`
cells before any new packet computation.  The genuinely new equality work is
the two affine complement classes, their fusion in `G`, and cross-carrier
positions not contained in a common calibrated carrier.  This claim does not
assert an ambient fusion classification of those remaining positions.

