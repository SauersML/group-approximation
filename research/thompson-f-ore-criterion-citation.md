---
rg: 2
id: thompson-f-ore-criterion-citation
kind: route
title: Import Kielak's Ore criterion and apply it to the zero-divisor-free group ring of F
target: thompson-f-amenable-iff-group-ring-is-ore
requires: []
---

Imports Kielak's theorem from the appendix of Bartholdi–Kielak arXiv:1605.09133v2:
a group ring without zero divisors is an Ore domain iff the group is amenable. It
then applies the standard chain: `F` acts faithfully by orientation-preserving
homeomorphisms of `(0,1)`, so `F` is left-orderable, so `F` has unique products,
so `K[F]` has no zero divisors.

**Source check (2026-09-12, lane `thompson-f-non-ore-witness`).** The appendix was
read from the arXiv v2 LaTeX source (`myhill.tex`, section "A characterization of
amenability via Ore domains, by Dawid Kielak"). Its theorem, verbatim up to macros:
"Let `G` be a group, and let `K` be a field such that `K G` has no zero divisors.
Then `G` is amenable if and only if `K G` is an Ore domain."
- *Hypotheses.* Only that `K` is a field and `K G` has no zero divisors. There is no
  hypothesis on subgroups or on the characteristic, so the field scope of the target
  is exactly the source's scope.
- *Proof, `=>`.* Tamari's argument: a Følner set turns the common-multiple equation
  into a linear system with more unknowns than equations.
- *Proof, `<=`.* Bartholdi's construction in the main text gives a finite extension
  `L` of `K` and a square matrix over `L G` that acts injectively on `(L G)^n` and has
  a zero last row. Restricting scalars gives an injection `(K G)^(dn) -> (K G)^(d(n-1))`.
  The classical field of fractions of an Ore domain is flat, and tensoring with it
  gives an injection `D^(dn) -> D^(d(n-1))` over a skew field `D`, which is impossible.
- *Sidedness.* The appendix writes the condition as "for every `a`, `s ≠ 0` there
  exist `b`, `t ≠ 0` with `at = bs`". For a group ring the involution `g -> g^-1`
  exchanges the left and right conditions, so the target's two-sided wording is
  equivalent to the source's.
