---
rg: 2
id: oos-graded-small-cancellation-scales-separate
kind: claim
title: In a graded small cancellation presentation the relator lengths of each layer are negligible against the injectivity radius of the next stage map
distinct_from:
  kazhdan-torsion-free-tarski-monster-satisfies-kk: that imports the existence of a graded small cancellation presentation for the torsion-free Tarski monster; this imports the quantitative scale separation that every such presentation satisfies.
artifacts:
  - research/oos-graded-small-cancellation-scales-separate-citation.md
---

**ESTABLISHED** by literature import: `oos-graded-small-cancellation-scales-separate-citation`.
Source: Olshanskii--Osin--Sapir, *Lacunary hyperbolic groups*, Geom. Topol. 13 (2009),
arXiv:math/0701365, Definition `classQ` and Lemma `asc`.

Let `⟨S | ⋃_{i≥0} R_i⟩` be a graded small cancellation presentation of a group `G`. That means a
`Q(.01, 10^6)`-presentation in the sense of OOS Definition `classQ`, with `S` finite. Put
`G_n = ⟨S | R_0 ∪ ... ∪ R_n⟩` and `r_n = r_S(G_n → G_{n+1})`, the injectivity radius. Then there
are positive sequences `ρ_n` (`n ≥ 1`) and a constant `D` such that:

- **(A1)** `|R| ≥ ρ_n` for every `R ∈ R_n` (condition `C_2`), and `max{|R| : R ∈ R_n} ≤ D ρ_n`
  for every `n ≥ 1` (condition `Q_3`);
- **(A2)** `ρ_n = o(ρ_{n+1})` and `ρ_n → ∞` (Lemma `asc`(c));
- **(A3)** `ρ_n = o(r_n)` (Lemma `asc`(d));
- **(A4)** `G_0` is hyperbolic (condition `Q_0`), and so is every `G_n` (Lemma `asc`(a)).

Reading of `O(ρ_n)` in (A1). `Q_3` asserts `8 max{|R| : R ∈ R_{n}} = O(ρ_n)`. `O` is asymptotic, so
the ratio is bounded for large `n`. For each of the finitely many small `n`, the maximum is a
finite number because `Q_3` asserts that it exists. So one constant `D` works for all `n ≥ 1`.
