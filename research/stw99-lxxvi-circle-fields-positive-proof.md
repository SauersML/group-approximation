---
rg: 2
id: stw99-lxxvi-circle-fields-positive-proof
kind: route
title: Split circle Cu into cancellative clutching classes and pointwise noncompact sections
target: stw99-lxxvi-circle-fields-over-simple-pure-fibers
requires:
  - stw99-lxxvi-circle-projections-cancel
artifacts:
  - research/artifacts/stw99-lxxvi-fourth-depth-audit-2026-08-30.md
---

Put `E=D tensor_min Z`.  Lin's stable-rank theorem gives stable rank one for
`D`; the simple stably finite Z-stable algebra `E` also has stable rank one.
Antoine--Dadarlat--Perera--Santiago, Theorem 3.7 in
[Recovering the Elliott invariant from the Cuntz semigroup](https://arxiv.org/abs/1109.5803),
gives natural decompositions

```text
Cu(C(T,D)) = V(C(T,D)) disjointUnion Lsc_nc(T,Cu(D)),
Cu(C(T,E)) = V(C(T,E)) disjointUnion Lsc_nc(T,Cu(E)),    (1)
```

with the mixed addition and order determined by pointwise evaluation.

On the noncompact summands, the first-factor map in (1) is pointwise
application of `Cu(D)->Cu(E)`.  That fiber map is an isomorphism by STW
Proposition 23.  It preserves compactness in both directions, so it gives an
isomorphism of the two `Lsc_nc` summands.

It remains to treat compact elements.  By
`stw99-lxxvi-circle-projections-cancel`, projections over `C(T,D)` cancel.
The standard circle clutching description therefore gives

```text
V(C(T,D)) ~= {0} disjointUnion (V(D)\{0}) times K_1(D).
```

The same description holds for `E` (alternatively, use Z-stability and full
projection cancellation).  The first-factor map respects these coordinates.
Its `V(D)` coordinate is an isomorphism by STW Lemma 22(ii), using pureness,
strict comparison, and cancellation in `D`; its `K_1` coordinate is an
isomorphism because `C->Z` is a KK-equivalence.  Hence the compact summands
in (1) are isomorphic as well.

All identifications used in (1) are natural for the first-factor embedding.
The component isomorphisms preserve the pointwise mixed order and addition,
so together they prove that the displayed Cu map is an isomorphism.
