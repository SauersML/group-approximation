---
rg: 2
id: sofic-permanence-closure-omits-simple-fa-nonsofic-groups
kind: claim
title: Extensions, graphs of groups, colimits and marked limits of sofic groups contain no finitely presented simple nonsofic FA group
distinct_from:
  gottschalk-counterexamples-lie-outside-the-permanence-closure: that closes the sofic groups under the landed permanence operations, including local embeddability and Arzhantseva--Gal extensions, and needs no property FA; this adds FA and survives arbitrary extensions, all graphs of groups and marked limits, so it also excludes permanence theorems not yet proved.
artifacts:
  - research/artifacts/fixed-host-permanence-closure-obstruction-2026-09-12.md
---

Let `Sigma` be a finitely presented simple group with Serre's property FA that
is not sofic. Let `D_Sigma` be the class of groups with no subgroup isomorphic
to `Sigma`. Then `D_Sigma` contains every sofic group and is closed under:

1. subgroups;
2. directed colimits with arbitrary structure maps;
3. extensions: if `N` is normal in `E` and both `N` and `E/N` lie in
   `D_Sigma`, so does `E`;
4. fundamental groups of graphs of groups with vertex groups in `D_Sigma`, for
   any graph, any edge groups and any edge maps;
5. limits in the space of finitely generated marked groups.

So no group built from sofic groups by these operations, in any order and any
number of times, contains `Sigma`. That includes every group the landed
surjunctivity permanence theorems produce from sofic groups: finitary split
extensions (their kernels are residually finite), graph folds, LEF-lamp graph
wreaths, RF-lamp permutational wreaths and doubles.

Why each operation fails to create `Sigma`:
- a finite presentation factors an embedding into a colimit through one stage;
- `Sigma ∩ N` is `1` or `Sigma`;
- FA puts `Sigma` inside a vertex stabilizer of the Bass--Serre tree;
- a marked limit eventually contains a nontrivial quotient of `Sigma`, which
  must be `Sigma` itself.

The full proof is Section 3 of the artifact.

This is a statement about proof architecture. It does not say that `Sigma` is
not surjunctive.
