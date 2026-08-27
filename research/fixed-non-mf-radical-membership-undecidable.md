---
rg: 2
id: fixed-non-mf-radical-membership-undecidable
kind: claim
title: One fixed finitely presented non-MF group has undecidable MF-radical membership
artifacts:
  - GroupApproximation/Sofic/FreeProductMFRadicalRetraction.lean
  - non_mf_group_notes.tex
distinct_from:
  single-finitely-presented-mf-radical-computer: there every hard word is promised to lie in the radical and only equality with one varies; here actual radical membership varies and is undecidable.
  finitely-presented-amenable-undecidable-word-problem: in that MF group radical membership is already its word problem; adjoining a fixed non-MF free factor makes the ambient group non-MF.
  fixed-mf-radical-membership-is-sigma2-complete: this proves undecidability, not FIN-hardness or second-level completeness.
---

There is one fixed finitely presented non-MF group `U` such that membership in
`Res_MF(U)` is undecidable.

Choose Cairn's fixed finitely presented non-MF group `E` and a fixed finitely
presented amenable group `A` with undecidable word problem, and set

```text
U = E * A.
```

Then `U` is finitely presented and non-MF.  For every word `a` in the `A`
factor,

```text
i_A(a) in Res_MF(U)  iff  a=1 in A.                       (RAD2)
```

Thus actual radical membership, not merely a promised word problem inside the
radical, is undecidable in one fixed finite presentation.  Combining with
[[mf-radical-membership-has-a-sigma2-upper-bound]] places this fixed radical in
`Sigma^0_2`, but does not establish `Sigma^0_2`-completeness.
