---
rg: 2
id: torsion-is-a-finite-datum-torsion-freeness-is-not
kind: claim
title: Having torsion survives relator truncation, so a finite-data argument never delivers torsion-freeness
distinct_from:
  finite-torsion-free-pattern-realizable-finitely-presented: that realizes a finite pattern inside a finitely presented TORSION-FREE group, using the torsion-free universal quotient to supply the adjective; this proves that the naive truncation of relators cannot supply it, which is why that node needs its extra mechanism.
  operator-mf-is-a-markov-property: that is about MF being a Markov property of finitely presented groups; this is about which torsion conditions survive passage to finitely presented approximations, and mentions no approximation property.
artifacts:
  - research/artifacts/torsion-free-transfer-covers-and-obstructions-2026-09-08.md
---

**ESTABLISHED.**  Let `G = F/R` with `F` free, and suppose `G` has torsion:
there is `w in F` with

```text
w not in R,        w^m in R,        m > 1.                              (TF1)
```

Write `R` as the increasing union of the normal closures `R_i` of finite
subsets of `R`, so that `F/R_i` is finitely presented and `F/R_i -> G`.  Then
for every `i` large enough that `w^m in R_i`,

```text
F/R_i has a nontrivial element of finite order,
```

namely the image of `w`, which is nontrivial because `R_i <= R` and
`w not in R`.  So every sufficiently late finitely presented approximation of
a group with torsion has torsion.

**Reading.**  The two conditions in `(TF1)` are finite data, and truncation
preserves them.  Torsion-freeness is not finite data and truncation does not
preserve it; a construction that produces finite presentability by keeping
finitely many relations therefore cannot deliver torsion-freeness as a
by-product.  This is why
`finite-torsion-free-pattern-realizable-finitely-presented` obtains the
adjective from the torsion-free universal quotient rather than from the
approximation, and why the finitely generated cover of
`free-abelianized-cover-is-torsion-free` cannot be made finitely presented by
discarding relators.

It excludes one argument, not one conclusion: nothing here says a torsion-free
finitely presented approximation does not exist.
