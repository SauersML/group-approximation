---
rg: 2
id: milhoj-rordam-traceless-family-quasitracial-ultraproduct
kind: claim
title: Traceless simple nuclear algebras finite up to matrix level n have an ultraproduct carrying a quasitrace
artifacts:
  - research/artifacts/stw01-certificates-products-universal-tests-2026-09-11.md
---

**ESTABLISHED (literature).**  There are unital separable C\*-algebras `P_n`
(`n >= 1`) with the following properties.

- They are all Morita equivalent to one unital simple separable nuclear
  C\*-algebra `P`, which is finite with `M_2(P)` properly infinite (Rørdam).
- `M_k(P_n)` is finite for `k <= n` and properly infinite for `k > n`.
- Each `P_n` is traceless, and for every free ultrafilter `omega` the
  ultraproduct `prod_omega P_n` admits a normalized 2-quasitrace.

These are Theorems 4.3, 4.4 and 4.6 of Milhøj–Rørdam, arXiv:2309.17412v2.  The
algebra `P` comes from Rørdam's crossed product `D x_alpha Z` (Acta Math. 191
(2003), arXiv:math/0204339v2, Section 6), where `D` is an inductive limit of
type I algebras and finiteness is certified by Euler classes over products of
2-spheres.  Milhøj–Rørdam also give a variant with `M_k(Q_n)` finite for
`k <= 2^n n` and `P_n = M_(2^n)(Q_n)`, whose ultraproduct contains the UHF
algebra of type `2^infinity` unitally.

**Open, as recorded by the source.**  It is not known whether
`prod_omega P_n` admits a tracial state.  The authors expect that it does.  If
it does not, it is a counterexample to Kaplansky's question.  That hole is
`stw01-rordam-family-ultraproduct-is-traceless`.  By Proposition 5.5 of the
same paper, the ultraproduct has a tracial state iff the `P_n` eventually admit
`(N, eps)`-almost traces for all `N` and `eps`.
