---
rg: 2
id: virtually-torsion-free-infinite-mf-radical-gives-seed-proof
kind: route
title: Trace the radical to a torsion-free finite-index subgroup and Higman-embed it
target: virtually-torsion-free-infinite-mf-radical-gives-seed
requires:
  - corona-finite-index-radical-heredity
  - torsion-free-higman-embedding
  - universal-mf-quotient
  - mf-positive-controls
  - nonhyperlinear-finite-augmentation-corner-kills-mf
artifacts:
  - research/corona-finite-index-radical-heredity.md
---

## Why sufficient

**Step 0: the finite radical is finite.**  Fix a torsion-free `E <= H` of
index `m`.  A finite normal `N` meets `E` trivially, so `N` embeds in the coset
space `H/E` and `|N| <= m`.  The product of two finite normal subgroups is
finite and normal.  So the finite normal subgroups form a directed family whose
orders are bounded by `m`.  Its union `W(H)` is therefore one finite normal
subgroup, of order at most `m`.

**Step 1: the dichotomy is exhaustive.**  `R = Rad_MF(H)` is normal.  If `R` is
finite, it is a finite normal subgroup, so `R <= W(H)`.  Contrapositively, if
`R` is not contained in `W(H)` then `R` is infinite.  If `R <= W(H)`, then for
every torsion-free finite-index `E` we have `R intersect E <= W(H) intersect E = 1`,
because `W(H)` is a finite group and `E` is torsion-free.  So case 1 has
`Rad_MF(E) = 1` by `corona-finite-index-radical-heredity`.

**Step 2: the radical survives in `E`.**  In case 2, `R` is infinite, and
`R intersect E` has index at most `[H:E]` in `R`.  So it is infinite, and in
particular nontrivial.  By `corona-finite-index-radical-heredity`,

```text
Rad_MF(E) = E intersect Rad_MF(H) = E intersect R != 1.
```

By `universal-mf-quotient`, `E` is not MF.

**Step 3: `E` is finitely generated and recursively presented.**  Let
`H = <X | R_H>` with `X` finite and `R_H` recursively enumerable.  Fix a finite
Schreier transversal `t_1 = 1, ..., t_m` for `E`, together with the finite
coset action of `X`.  Reidemeister--Schreier then gives:

- a finite generating set `{t_i x t_(xi)^-1}` for `E`;
- relators obtained by rewriting the words `t_i r t_i^-1`, for `r` in `R_H`.

The rewriting process is a fixed finite-state algorithm.  Its output on the
recursively enumerable input is therefore recursively enumerable.  Only
existence is needed, not uniformity in `H`.

**Step 4: Higman.**  `E` is torsion-free and recursively presented.  By
`torsion-free-higman-embedding` (Chiodo), `E` embeds in a finitely presented
torsion-free `T`.  Subgroups of MF groups are MF (`mf-positive-controls`), so
`T` is not MF.

**Converse.**  A seed `T` is finitely presented, hence recursively presented.
It is torsion-free, so `W(T) = 1`, and `Rad_MF(T) != 1` by
`universal-mf-quotient`.

**Corollary.**  `nonhyperlinear-finite-augmentation-corner-kills-mf` needs
only countability and a finite `K`.  It gives `K <= Rad_MF(H)`.  If `K` is not
contained in `W(H)`, then `R` is not contained in `W(H)` either, and case 2
applies.

## Property-T audit

The route uses the following, and nothing else:

- the heredity induction, which is block-monomial and purely algebraic;
- Chiodo's embedding, which is combinatorial;
- the defining property of the universal MF quotient;
- the positive controls;
- the corner theorem, which the goal's own audit already lists as free of
  `(T)`.

No Kazhdan input appears.
