---
rg: 2
id: mf-reflection-colimit-calculus-proof
kind: route
title: Use the MF adjunction to represent cocones into every MF target
target: mf-reflection-colimit-calculus
requires:
  - countable-mf-groups-are-epireflective
  - mf-relation-closure
---

For every countable MF group `M`, the adjunction and the ordinary colimit
universal property give natural bijections

```text
Hom_MF(R_MF(C),M)
 ~= Hom_Grp(C,M)
 ~= lim_i Hom_Grp(D_i,M)
 ~= lim_i Hom_MF(R_MF(D_i),M).
```

Therefore `R_MF(C)` represents cocones from the reflected diagram and proves
`(MC1)`.  Applying the same calculation to the objectwise unit
`D->R_MF o D` proves `(MC2)`.

Free products, amalgams, coequalizers, and HNN extensions are the standard
group colimits, so the first four formulas are specializations.  A presented
group is the coequalizer of the relator words and the trivial words in the
free group.  The relation-closure theorem identifies the kernel of its unit
with `mfroot(<<S>>)/<<S>>`, giving the fifth formula.
