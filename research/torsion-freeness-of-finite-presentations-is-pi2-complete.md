---
rg: 2
id: torsion-freeness-of-finite-presentations-is-pi2-complete
kind: claim
title: Torsion-freeness of finitely presented groups is Pi-zero-two complete
artifacts:
  - research/artifacts/second-level-rice-theorem-2026-08-26.md
distinct_from:
  torsion-freeness-recognition-is-pi2-complete: that is the theorem for recursive and enumerated presentations, where the switch alone suffices; this crosses to finite presentations through the compiler and its torsion-free positive rope, and is the first property other than MF whose finite-presentation cell is closed at the second level.
  mf-recognition-finite-presentations-is-pi2-complete: that is the MF cell; this is the torsion-free cell, obtained from the same compiler with a different seed and a different property of the positive branch.
---

ESTABLISHED.  For the recursive coding of finite group presentations,

```text
TORSIONFREE_fp   is Pi^0_2-complete,
HASTORSION_fp    is Sigma^0_2-complete.                            (TFP1)
```

Membership is the `Pi^0_2` normal form of
[[torsion-freeness-recognition-is-pi2-complete]] specialized to finite
relator lists.  Hardness is
[[finite-presentation-rice-criterion-via-the-fixed-positive-rope]] with
`P` = torsion-freeness (hereditary), (C1) supplied by
[[mf-compiler-positive-branch-is-torsion-free]] and (C2) by the seed
`Z/2`.

This closes one of the open cells of
[[arithmetical-complexity-table-of-group-properties]] and shows that
`Pi^0_2`-completeness on finite presentations is not special to MF: the
obstacle in the remaining cells is exactly whether the fixed rope has the
property in question.

## Two generators

The same completeness holds for two-generator finite presentations.  The
Higman--Neumann--Neumann embedding of a finitely presented group into a
two-generator finitely presented group is explicit and computable, and it
is an iterated HNN extension of the given group, so torsion elements of
the envelope are conjugate into the base: the envelope is torsion-free
exactly when the base is.  Applying it to the compiler's output preserves
both branches --- torsion-free on `INF`, and containing `Z/2` on `FIN` ---
so `INF` reduces to torsion-freeness of two-generator finite
presentations.

## The whole order family, at once

For each integer `n >= 2` the property "has no element of order `n`" is
hereditary, isomorphism invariant, holds for the rope (which is
torsion-free) and fails for `Z/n`, which is finitely presented.  So the
same criterion gives

```text
{ P : Carrier(P) has no element of order n }   is Pi^0_2-complete,     (TFN)
```

for every `n >= 2`, with the `Pi^0_2` upper bound as in
[[torsion-freeness-recognition-is-pi2-complete]] (universal quantifier
over words of a difference of two r.e. events, with the exponent fixed).
Taking the intersection over `n` recovers torsion-freeness; taking `n`
prime recovers "no `p`-torsion".  All of these cells are therefore closed
at the second level on finite presentations, which is the widest family of
finite-presentation cells now settled.
