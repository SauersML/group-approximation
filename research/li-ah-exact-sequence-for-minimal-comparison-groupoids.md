---
rg: 2
id: li-ah-exact-sequence-for-minimal-comparison-groupoids
kind: claim
title: "Xin Li: Matui's AH exact sequence holds for minimal ample groupoids with comparison, including all purely infinite minimal ones"
artifacts:
  - research/artifacts/hl-bh-a2-boundary-hosts-2026-09-14.md
---

**ESTABLISHED (import).** Let `G` be an ample groupoid whose unit space is locally
compact Hausdorff without isolated points, and assume `G` is minimal and has comparison.
Then there is an exact sequence

```text
H_2(D(G)) -> H_2(G) -> H_0(G, Z/2) -> H_1(F(G)) -> H_1(G) -> 0,
```

where `F(G)` is the topological full group and `D(G)` its commutator subgroup.
Purely infinite minimal ample groupoids have comparison. Here `G` is purely infinite
minimal when for all compact open `U, V` in the unit space with `V` nonempty there is a
compact open bisection `σ` with `s(σ) = U` and `r(σ) ⊆ V`.

Consequence used in this graph: if `H_0(G; Z/2) = 0` and `H_1(G) = 0` for such `G`,
then `F(G)` is perfect.

Source: X. Li, *Ample groupoids, topological full groups, algebraic K-theory spectra and
infinite loop spaces*, Forum Math. Pi, arXiv:2209.08087, Corollary `cor:AHConj` and the
paragraph at TeX l.804.

Route: `li-ah-exact-sequence-citation`.
