---
rg: 2
id: oos-lacunary-hyperbolic-short-relator-stages
kind: claim
title: A lacunary hyperbolic group is approximated by finitely presented stages whose relator lengths are negligible against their injectivity radius, and a finitely presented one is hyperbolic
distinct_from:
  oos-graded-small-cancellation-scales-separate: that imports scale separation for a given graded small cancellation presentation; this imports the stage construction that OOS run for every lacunary hyperbolic group, with no presentation assumed.
artifacts:
  - research/oos-lacunary-hyperbolic-short-relator-stages-citation.md
---

**ESTABLISHED** by literature import: `oos-lacunary-hyperbolic-short-relator-stages-citation`.
Source: Olshanskii--Osin--Sapir, *Lacunary hyperbolic groups*, Geom. Topol. 13 (2009),
arXiv:math/0701365. The pieces used are Section 1.1, the proof of 1) ⇒ 3) in Theorem 3.3, and
Theorem 8.1 of the Kapovich--Kleiner appendix.

A finitely generated group `K` is **lacunary hyperbolic** if one of its asymptotic cones is an
R-tree. Asymptotic cones are taken with scaling constants `d_n → ∞`.

Let `K = ⟨S⟩` be lacunary hyperbolic, with `S` finite. Let `d = (d_n)` be the scaling sequence
from the OOS proof, so `Con^ω(K, d)` is an R-tree. Let `H_n = ⟨S | R_n⟩`, where `R_n` is the set of
labels of all cycles in the ball of radius `d_n` about `1` in `Γ(K, S)`. Then:

- **(S1)** `K` is a quotient of `H_n`, and the canonical map `H_n → K` is injective on the ball
  of radius `d_n`.
- **(S2)** There is a constant `C_2 > 0` and a strictly increasing sequence `n(k)` such that
  `H_{n(k)}` has a finite presentation over `S` whose relations have length at most
  `d_{n(k)} / (C_2 k)`.
- **(S3)** (Kapovich--Kleiner, Theorem 8.1) A finitely presented group with an asymptotic cone
  that is an R-tree is hyperbolic. So a finitely presented lacunary hyperbolic group is hyperbolic.
- **(S4)** A group quasi-isometric to a lacunary hyperbolic group is lacunary hyperbolic.
