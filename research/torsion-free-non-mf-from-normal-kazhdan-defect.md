---
rg: 2
id: torsion-free-non-mf-from-normal-kazhdan-defect
kind: route
title: Apply the normal-Kazhdan obstruction to the Fournier-Facio torsion-free group
target: torsion-free-finitely-presented-non-mf
requires: [normal-kazhdan-defect-non-mf, fournier-facio-torsion-free-skeleton, defect-normally-generates-torsion-free-quotient]
artifacts:
  - research/artifacts/router-detector-torsion-free-non-mf-2026-08-22.md
  - GroupApproximation/Sofic/TorsionFreeFullMFRadical.lean
  - GroupApproximation/Sofic/NormalKazhdanMFRadical.lean
---

## Why sufficient

Let `G` be the routed modification of the Fournier-Facio group: finitely
presented, torsion-free, with property (T), compression core
`(Gamma, t_1, c in J)`, and a copy `S'` of the finitely presented simple
torsion-free group `S` inside its compression defect
(`fournier-facio-torsion-free-skeleton`).

Put `K = <<S'>>^G`.  The established strongest form of
`defect-normally-generates-torsion-free-quotient` is not merely that `K` has
finite index or inherits property (T), but

```text
K = G.
```

Indeed, Hull's target words are drawn from the normal closure of `S`, so the
image `S'` normally generates the quotient.  The compression defect contains
`S'`: for the protected `1 != s' in S'`, centrelessness supplies
`x in S' <= Gamma` with `[s',x] != 1`; the normal intersection with the
simple group `S'` is therefore all of `S'`.  Since the defect is normal and
`<<S'>>^G=G`,

```text
defectNormal = G.
```

Property (T) of `G` comes from the other common-quotient map, from the
torsion-free hyperbolic Kazhdan group onto `G`.

`normal-kazhdan-defect-non-mf` now applies with the normal Kazhdan subgroup
`K=G`: every homomorphism from `G` into the unitary group of a norm matrix
corona kills every element of `G`.  Thus every such homomorphism is trivial,
the MF residual is all of `G`, and the nontrivial group `G` is not MF — while
being torsion-free and finitely presented.

This is the primary route into the root and is complete.  Its analytic half
is machine-checked and torsion-free; its group-theoretic half is the audited
Hull--Osin routing argument.  The attached router--detector artifact gives the
complete synthesis and connects the same proof to the stronger established
node `defect-saturation-full-mf-radical` and to asymptotic triviality.
