---
rg: 2
id: linnell-dimension-equals-skew-field-rank
kind: claim
title: For torsion-free groups in Linnell's class, von Neumann dimension of induced modules equals rank over the Linnell skew field
distinct_from:
  strong-atiyah-passes-to-locally-indicable-extensions: that passes the strong Atiyah conjecture to locally indicable extensions (Jaikin-Zapirain--López-Álvarez Prop 6.5); this imports Linnell's class-C theorem together with Lück's comparison of N(G)-dimension and D(G)-rank.
artifacts:
  - research/artifacts/fpbs-locally-free-fixed-pseudocost-2026-09-17.md
---

**ESTABLISHED (literature import).** Let `G` be a torsion-free group in
Linnell's class `C`, for example a free group. Let `D(G)` be the rational
closure of `CG` in `U(G)`. Then:
- `D(G)` is a skew field;
- every `CG`-module `M` satisfies
  `dim_(N(G))(N(G) ⊗_(CG) M) = dim_(D(G))(D(G) ⊗_(CG) M)`.

A skew subfield of `U(G)` is division closed. So `D(G)` contains the division
closure of `Q[G]` in `U(G)`.

Route: `linnell-dimension-equals-skew-field-rank-citation`.
