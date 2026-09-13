---
rg: 2
id: leary-groups-with-cofinite-s-are-type-fhn
kind: claim
title: "Leary's groups G_L(S) with cofinite S are of type FH_n whenever L is (n-1)-acyclic and pi_1(L) is of type FP_n"
distinct_from:
  isolated-type-fn-vertex-stabilizers-give-type-fhn: that claim is the general replacement principle for isolated singular vertices; this applies it to Leary's branched cube complexes
  some-type-fpn-group-is-not-of-type-fhn: that claim asks for a separating group; this shows Leary's cofinite family does not provide one over the integers
artifacts:
  - research/artifacts/zp-fpn-fhn-2026-09-13-part3.md
---

Let `n ≥ 2`, `L` a finite connected flag complex with `H̃_i(L; ℤ) = 0` for
`i ≤ n−1` and `π_1(L)` of type `FP_n`, and `S ⊆ ℤ` with `ℤ − S` finite. Then
Leary's group `G_L(S)` (arXiv:1512.06609) acts freely, with finitely many
orbits of cells, on an `(n−1)`-acyclic CW complex. That is, `G_L(S)` is of
type `FH_n`.

Leary proves these groups are `FP_n`. He writes that for `ℤ − S` finite "we
do not know whether `G_L(S)` is necessarily `FH(R)`". This claim settles the
finite-degree version `FH_n` over `ℤ`. It does not settle `FH`.

Proof (Theorem L of the artifact):
1. For `m ≥ max |ℤ − S|` the slab `X(m)` of Leary's branched cube complex is
   `(n−1)`-acyclic, because enlarging it only cones off copies of `L`.
2. Its only nontrivial stabilizers are isolated vertices with cone
   neighbourhoods over `𝕊(L̃)` and stabilizer `π_1(L)`, which is finitely
   presented and `FP_n`.
3. `isolated-type-fn-vertex-stabilizers-give-type-fhn` replaces those cones
   by mapping cylinders into `(n−1)`-connected free cocompact complexes.

**Consequence.** Assume `π_1(L)` is of type `FP_n`. Combined with Leary's
results for finite `S` and for `S`, `ℤ − S` both infinite, every `G_L(S)` of
type `FP_n` is of type `FH_n`. Leary's family cannot answer Zaremsky Problem
1.4 negatively.
