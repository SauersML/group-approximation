---
rg: 2
id: every-group-is-binary-surjunctive
kind: claim
title: Every group is surjunctive for the two-symbol full shift
distinct_from:
  gottschalk-surjunctivity-conjecture: that is surjunctivity over every finite alphabet; this is the two-symbol alphabet only, implied by the conjecture and, through product alphabets, by surjunctivity over any even alphabet.
artifacts:
  - research/artifacts/boolean-core-alphabets-and-network-coding-2026-09-12.md
---

**OPEN.** For every group `G`, every injective cellular automaton on `{0,1}^G` is surjective.

By `strict-rule-pairs-pass-to-product-alphabets`, this follows from surjunctivity over any even
alphabet. It gives the full conjecture if strictness descends to two symbols
(`surjunctivity-failure-descends-to-binary-alphabet`).

## Attempts

- **The linear binary case.** Linear rules over `F_2` are one-sided inverse pairs in `F_2[G]`, so
  the linear binary case is Kaplansky direct finiteness over `F_2`. That is the lane of
  `leavitt-unit-group-algebra-not-directly-finite` and is not settled.
- **Nonlinear binary rules.** The Boolean core in the artifact contains no binary obstruction
  beyond the filters: discrete forward tables, one-relay shapes, and the transposed 2 x 2 core.
  The design filters of the region (nonsofic forward core, holonomy normal form, amenable decoder
  memory) apply unchanged at two symbols.
- **Low-degree reduction (gk-n-highalpha, pending verification).** Theorem 7 of
  `research/artifacts/low-degree-strict-pairs-linear-parts-2026-09-12.md`
  (`low-degree-strict-pairs-have-one-sided-linear-parts`) says a strict pair over `F_q` with
  `deg sigma * deg tau < q` has one-sided-inverse linear parts, a matrix Kaplansky pair over
  `F_p[G]`. At `q = 2` that bound covers only affine designs, so it adds nothing beyond the linear
  case. Every nonlinear binary design has degree product at least `2 = q`, the regime where
  `x^2 = x` feeds higher decoder terms into degree one. So a binary counterexample that is not a
  disguised Kaplansky pair must be nonlinear in exactly that regime.
