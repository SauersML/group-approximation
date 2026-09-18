---
rg: 2
id: fpbs-benjamini-schramm-via-no-fiid-sparse-spines
kind: route
title: Deduce strict thresholds from the absence of factor-of-iid sparse spines
target: fpbs-benjamini-schramm-universal
requires:
  - fpbs-no-fiid-sparse-spines-on-nonamenable-groups
  - fpbs-fiid-soft-collapse-iff-fiid-sparse-spines
---

**Audit note (2026-09-17).** Referee lens 3 reports that this route is dead at
its hole: `F_2 x Z^2` has FIID sparse spines (unique supercritical `Z^2`
clusters in each fibre, joined by iid-labelled `F_2`-edges, density
`theta_{Z^2}(b) -> 0` as `b -> 1/2`), so
`fpbs-no-fiid-sparse-spines-on-nonamenable-groups` is false as stated. The
counterexample is recorded under Attempts of the hole and has not yet been
refereed itself.

Let `Gamma` be nonamenable and finitely generated, and let `S` be a finite
symmetric generating set.

By the hole, `Gamma` has no FIID sparse spines. Part (i) of
`fpbs-fiid-soft-collapse-iff-fiid-sparse-spines` says that
`p_c(Cay(Gamma,S)) = p_u(Cay(Gamma,S))` would produce such spines, and part
(ii) makes this independent of `S`. So `p_c < p_u`.

Every route of this form can fail at the hole:

* `fpbs-kazhdan-sparse-spines` asserts the negation on infinite Kazhdan groups;
* a factor-of-iid spine on any single nonamenable group kills this route
  without refuting the goal.

Compared with `fpbs-benjamini-schramm-two-cost-cases`: that route splits by
maximal cost and leaves the fixed-price-one kernel with no object to aim at.
This route names the object, factor-of-iid sparse spines, whose absence
suffices on every group.
