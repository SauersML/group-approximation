---
rg: 2
id: decidable-amenable-groups-have-no-recursive-folner-bound
kind: claim
title: For every recursive U there is a finitely generated elementary amenable group with solvable word problem whose Følner function is not bounded by U
distinct_from:
  folner-functions-of-fp-amenable-groups-have-no-recursive-bound: that asks the same for finitely PRESENTED amenable groups, the negative answer to Gromov's question, and stays open for want of an amenable finitely presented envelope; this is the finitely generated, decidable version, settled here from Brieussel--Zheng diagonal products.
  recursive-amenable-classes-have-uniform-folner-bounds: that gives one recursive bound for each c.e. class of amenable presentations; this shows the class of decidable finitely generated amenable groups has no such bound, so it lies in no c.e. class of amenable presentations.
  iterated-wreath-products-of-z-have-tower-folner-functions: that gives towers of each fixed height from one uniform family, all under one recursive bound; this beats every recursive bound, with one group per bound.
  fp-simple-dehn-functions-have-no-recursive-upper-bound: that is about Dehn functions of finitely presented simple groups; this is about Følner functions of decidable amenable groups, with no simplicity and no finite presentation.
---

**ESTABLISHED** by `decidable-amenable-groups-have-no-recursive-folner-bound-proof`.
This is a direct derivation from Brieussel--Zheng, arXiv:1510.08040v2, whose
cited statements were read at source on 2026-09-18. It has not been
independently reviewed, and no priority is claimed: it is close to folklore
given that paper.

## Statement

Let `F_(Δ,X)(n)` be the least size of a finite `Ω ⊂ Δ` with
`|Ω \ xΩ| <= |Ω|/n` for every `x in X`. Write `f ≼ U` when `f(n) <= C U(Cn)`
for some `C` and all `n`.

**Theorem.** For every recursive non-decreasing `U: N -> N` there is a
diagonal product `Δ_U`, with finite generating set `X`, such that:
1. `Δ_U` is finitely generated and elementary amenable;
2. `Δ_U` has solvable word problem;
3. `F_(Δ_U, X)` is not `≼ U`. In fact, for every `C` there are infinitely many
   `n` with `F_(Δ_U, X)(n) > C U(Cn)`.

Moreover `U -> Δ_U` is uniform. From an index of a total recursive `U` one
computes a solution of the word problem of `Δ_U`.

## Reading

- By Cavaleri's Theorem 3.1 (`recursive-amenable-classes-have-uniform-folner-bounds`)
  each single `Δ_U` has a recursive Følner bound. So the theorem is necessarily
  about infinitely many groups.
- By Cavaleri's Corollary 3.6, the class of decidable finitely generated
  amenable groups is contained in no recursively enumerable class of
  presentations of amenable groups.
- The construction uses the totality of `U`. That is forced, because a
  computable map `e -> Δ_e` with every `Δ_e` amenable would have one recursive
  bound.
- This supplies the "inputs exist" half of Attempt 1 in
  `folner-functions-of-fp-amenable-groups-have-no-recursive-bound`: recursively
  presented, indeed decidable, groups beyond every recursive bound. The
  finitely presented amenable envelope is still missing there.
