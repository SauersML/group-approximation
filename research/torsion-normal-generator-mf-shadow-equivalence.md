---
rg: 2
id: torsion-normal-generator-mf-shadow-equivalence
kind: claim
title: MF invisibility and operator-to-HS shadow invisibility coincide on a torsion normal generator
artifacts:
  - notes/EXACT_CORONA_DIMENSION_AND_HILBERT_HOTEL.md
  - non_mf_groups_exist.tex
---

**ESTABLISHED.**  Let `G` be finitely generated and let `a in G` have finite
order.  Suppose the normal closure of `a` contains a finite generating set of
`G`.  Write `Rad_MF(G)` for the norm-corona MF radical and
`R_(infinity->2)(G)` for the subgroup killed in normalized
Hilbert--Schmidt norm by every operator-norm asymptotic representation.  Then

```text
a in Rad_MF(G)  iff  a in R_(infinity->2)(G).          (MSE1)
```

The forward implication holds for every group.  The reverse implication is
specific to the finite-order normal-generator geometry: any norm-corona map
which sees `a` reblocks to an operator-norm asymptotic representation in
which `a` has a fixed positive normalized-Hilbert--Schmidt displacement.

If `G` is nontrivial, finitely generated, simple, and contains torsion, then
both residuals are normal and `(MSE1)` gives the global identity

```text
Rad_MF(G)=R_(infinity->2)(G).                          (MSE2)
```

Hence a simple torsion-marked group is a full MF black hole exactly when
every operator-norm asymptotic representation is pointwise
Hilbert--Schmidt trivial.  This equivalence requires neither a uniform
separation profile nor a priori control of the coordinate dimensions.
