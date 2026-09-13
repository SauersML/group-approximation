---
rg: 2
id: thompson-f-has-no-near-geodesic-automatic-structure
kind: claim
title: No automatic structure for Thompson's group F over x0, x1 accepts, for every element, a word within a fixed additive constant of its geodesic length
distinct_from:
  thompson-f-is-not-automatic: that excludes every automatic structure over every finite generating set; this excludes only structures over {x0, x1} whose languages contain near-geodesic representatives
  thompson-f-is-automatic: that is the open affirmative answer; this established fact constrains any automatic structure over {x0, x1} to words with unbounded additive excess
---

**ESTABLISHED** through `thompson-f-has-no-near-geodesic-automatic-structure-citation`.

J. D. Hauze, *Restrictions on potential automatic structures on Thompson's group
F*, PhD dissertation, Binghamton University (2017), arXiv:1801.01965v1,
Theorem 1.1, verbatim:

> Let L be a language over the alphabet X = {x0, x1, x0^-1, x1^-1} and assume
> there is a non-negative integer c so that for every element g ∈ F there is a
> single word w ∈ L such that w represents g and |w| <= |g|_X + c. Then L cannot
> be a subset of the language associated with an automatic structure for F.

The case `c = 0` says an automatic structure for `F` cannot contain a geodesic
representative of each element. The dissertation reports that this recovers
Belk's result, from Chapter 6 of Belk's thesis, that `F` is not weakly
geodesically automatic.

Scope: one generating set and additive excess only. Automatic structures with
uniqueness consist of multiplicative quasigeodesics (see
`zaremsky-2-02-thompson-f-automatic`), so this does not decide Zaremsky
Problem 2.2.
