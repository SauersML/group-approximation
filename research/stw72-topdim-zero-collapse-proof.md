---
rg: 2
id: stw72-topdim-zero-collapse-proof
kind: route
title: Import the zero-dimensional Global Glimm theorem and apply Kirchberg--Rordam
target: stw72-topdim-zero-wpi-is-purely-infinite
requires: []
artifacts:
  - research/artifacts/stw72-topdim-zero-literature-import-2026-08-30.md
---

The forward implication is valid for every C-star algebra.  Conversely,
suppose that `A` is weakly purely infinite and has topological dimension
zero.  Weak pure infiniteness makes `A` nowhere scattered: this is
Thiel--Vilalta, Example 3.3, as used explicitly in Ng--Thiel--Vilalta,
[Corollary 2.5](https://doi.org/10.1112/blms.70343).

Ng--Thiel--Vilalta, [Theorem
2.3](https://doi.org/10.1112/blms.70343), proves without a separability
assumption that a topological-dimension-zero C-star algebra has the Global
Glimm Property if and only if it is nowhere scattered.  Hence `A` has the
Global Glimm Property.  Kirchberg--Rordam, Proposition 4.15 of
[*Non-simple purely infinite C-star
algebras*](https://doi.org/10.1353/ajm.2000.0021), characterizes pure
infiniteness as weak pure infiniteness together with the Global Glimm
Property.  Therefore `A` is purely infinite.

This is also the exact direct Theorem 2.1 of Elliott--Rouzbehani,
[*Weakly Purely Infinite C-star algebras with Topological Dimension Zero are
Purely Infinite*](https://mathreports.ca/article/weakly-purely-infinite-c-algebras-with-topological-dimension-zero-are-purely-infinite/),
C. R. Math. Rep. Acad. Sci. Canada 45(4) (2023), 87--91.  The
Ng--Thiel--Vilalta argument supplies an independent dependency audit through
the Global Glimm characterization.  Elliott--Rouzbehani, Corollary 2.2,
further identifies this condition with strong pure infiniteness.  Thus all
three notions in STW Problem LXXII coincide under topological dimension zero;
the additional separability and nuclearity assumptions in that corollary
attach only to its further equivalence with `O_infinity`-absorption, not to
the three pure-infiniteness conditions.
