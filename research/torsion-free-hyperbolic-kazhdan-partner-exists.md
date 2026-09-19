---
rg: 2
id: torsion-free-hyperbolic-kazhdan-partner-exists
kind: claim
title: A finitely presented torsion-free non-elementary hyperbolic Kazhdan group exists
distinct_from:
  fournier-facio-torsion-free-skeleton: that claim records a published compression configuration and mentions this partner only as one item on its torsion-free menu; this one isolates the partner as a standalone input with its own sources and its own degeneracy guard.
  kazhdan-envelope-needs-a-bespoke-relative-router: that claim argues the envelope step should be rebuilt in-repo because the repository has no hyperbolic apparatus; this one is the literature existence statement that the routing arguments actually consume, and takes no position on formalizing it.
  common-quotient-onto-normal-subgroup: that claim is a small-cancellation construction taking two acylindrically hyperbolic groups as given; this one supplies one of the two groups.
artifacts:
  - research/artifacts/arithmetic-single-defect-saturation-2026-08-23.md
---

There is a group `H` that is simultaneously

```text
infinite, non-elementary, finitely presented, torsion-free,
word-hyperbolic, and Kazhdan.
```

**The non-elementary clause is not decoration.**  The unqualified sentence "a
torsion-free hyperbolic group with property (T) exists" is satisfied by the
**trivial group**: a finite group is hyperbolic (its word metric is bounded)
and Kazhdan, and torsion-free plus finite means trivial.  Any route that
discharges the partner with a finite group has proved nothing, and the
repository's `HyperbolicKazhdanPartner` structure carries `Infinite` and
`hyperbolic` fields for exactly this reason.  Non-elementary is what the
consumers need: it is the hypothesis that makes `H` acylindrically hyperbolic
and so admissible as a factor in Hull's common-quotient theorem.

**Who consumes it.**  Every routing argument in the torsion-free program that
uses Hull as a black box needs an acylindrically hyperbolic Kazhdan partner to
donate property (T) to the common quotient — the source never can, because it
does not surject onto the quotient.  Until this node existed the input was used
in prose by `single-shadow-word-saturation-compiler-proof` ("a fixed finitely
presented hyperbolic Kazhdan group"), by the Fournier--Facio skeleton's
torsion-free menu, and by `defect-saturation-from-arithmetic-source`, without
appearing anywhere as a statement.  Recording it makes the trust surface of
those routes honest; it does not make any of them weaker.

**Not formalized, and not cheaply formalizable.**  The repository can state
hyperbolicity (`Algebra/HyperbolicGroup.lean`, four-point condition) but the
lattice route needs hyperbolicity to survive a finite-index passage, which is
quasi-isometry invariance, which needs the Morse lemma; arithmetic on the
four-point condition provably cannot substitute, since transporting it through
a `(K,C)`-quasi-isometry leaves a `K^2` that kills the inequality.  This node is
therefore a literature import, and every route through it inherits that.
