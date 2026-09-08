---
rg: 2
id: cornulier-non-hopfian-kazhdan-groups-are-mf
kind: claim
title: The finitely presented non-Hopfian Kazhdan groups are MF with trivial Kazhdan defects
distinct_from:
  cornulier-kazhdan-groups-are-central-quotients-of-linear-groups: that is the imported structural identification of the family; this is the analytic conclusion, that they are MF and carry no Kazhdan compression defect.
  central-quotients-of-residually-finite-groups-are-mf: that is the general theorem; this is its application to one published family, which is the family the proper-self-embedding constraint makes the natural candidate source.
  kazhdan-defects-vanish-in-central-quotients-of-rf-groups: that is the general defect statement; this names the family it removes from consideration.
  affine-perfect-lamp-wreath-has-locally-finite-mf-radical: that is a construction of a sofic non-MF group from a Kazhdan self-embedding; this is the negative result that the published non-Hopfian Kazhdan family cannot play that role directly, because those groups are themselves MF.
artifacts:
  - research/artifacts/central-quotient-rf-exclusion-2026-09-08.md
---

**ESTABLISHED.**  Every group in Cornulier's finitely presented
non-Hopfian Kazhdan family is MF, and every one of its property-(T)
subgroups `L` has

```text
D_G(L) = {1}.                                                     (CN2)
```

So this family is **excluded** as a direct source of compression-defect
examples, even though it satisfies the algebraic demand of
`defect-forces-proper-self-embedding` — its members are non-Hopfian, hence
admit proper self-surjections, and they are Kazhdan and finitely
presented.

The exclusion is of a candidate source, not a non-MF construction.  It
does not say that a group built **over** such a family is MF: the
wreath-product constructions in
`kazhdan-self-embedding-has-sofic-perfect-lamp-non-mf-family` and its
instances are not central quotients of residually finite groups, and are
untouched.  It also settles nothing about
`locally-finite-defect-subgroup-dies-in-every-corona`.

DERIVATION
cornulier-non-hopfian-kazhdan-mf-proof
