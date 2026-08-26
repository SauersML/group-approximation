---
rg: 2
id: hyperlinear-recognition-undecidable
kind: claim
title: Hyperlinearity of finitely presented groups is undecidable
distinct_from:
  approximation-property-recognition-dichotomy: that is the established two-sided theorem; this is the assertion that side (B) is the true side, which is open and equivalent to the goal.
  non-hyperlinear-group: that asks for a group; this asks for an algorithmic impossibility, and the two are equivalent by the dichotomy, so this is the goal seen from the computability side, where MIP-star-equals-RE-style reductions can be attempted.
  mf-recognition-undecidable: that is the MF statement and is established; this is the hyperlinear statement, which is open because no non-hyperlinear group is known.
---

OPEN.  The set `HYP_fp` of finite presentation codes whose group is
hyperlinear is not computable.

By [[approximation-property-recognition-dichotomy]] this is equivalent to
the existence of a non-hyperlinear group (the converse direction, a
non-hyperlinear group makes hyperlinearity Markov, is clause (a) of
[[second-level-rice-theorem-for-local-approximation-properties]] and is not
recorded as a route so that the graph stays acyclic), and once true it automatically
strengthens to `Pi^0_2`-completeness of hyperlinearity on two-generator
recursive presentations.  The value of stating it separately is the attack
surface: a proof need not exhibit a group.

## What a proof must deliver

A computable map from an undecidable index set `S` (halting, or directly
`INF`) to finite presentations `e |-> G_e` with

```text
e in S      ==>  G_e is hyperlinear,
e not in S  ==>  G_e is not hyperlinear,                             (HU1)
```

or the same with the two sides exchanged; by
[[local-approximation-properties-are-marked-closed]] the negative side may be
certified by a single finite table with no Hilbert--Schmidt model at a
single tolerance.  The template is MIP* = RE (Ji--Natarajan--Vidick--Wright--
Yuen): a halting-controlled family of games whose tensor-product value is
`1` on halting inputs and at most `1/2` otherwise; the failure of Connes'
embedding follows because the commuting-operator value is co-r.e.
approximable.  For groups the analogous compression would have to preserve
**exact** relations on the positive side, the perfect-completeness obstacle
recorded in [[taller-vidick-lcs-re-hardness]] and in the audit
`research/artifacts/computer-science-framing-audit-2026-08-21.md`.

## What does not suffice

* Undecidability of the word problem, or of MF, transfers nothing: the
  Adian--Rabin construction needs a forbidden hyperlinear-free seed, which is
  the goal itself.
* An RE-hard *value gap* with completeness `1 - epsilon`
  ([[taller-vidick-lcs-re-hardness]]) does not give (HU1): a value `1 - eps`
  strategy yields only approximate relations and no group.
* A `Pi^0_2` upper bound ([[nonhyperlinear-presentation-codes-have-a-sigma2-upper-bound]])
  is not evidence either way.
