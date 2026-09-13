---
rg: 2
id: locally-universal-group-factor-group-is-nonhyperlinear
kind: claim
title: A countable group whose group von Neumann algebra is locally universal is not hyperlinear
distinct_from:
  hyperlinear-iff-group-factor-embeds-in-hyperfinite-ultrapower: that is the dictionary between hyperlinearity and Connes embeddability of L(G); this uses it, together with the failure of the Connes embedding problem, to show that a locally universal L(U) can never belong to a hyperlinear U.
  non-ru-bcs-is-satisfiable-in-a-group-factor: that asks for an exact model of the non-RU constraint system inside some group factor; local universality of L(U) gives models of every separable tracial von Neumann algebra only inside ultrapowers of L(U), which is a different, ultrapower-level condition on one fixed host.
---

**Statement.**  Let `U` be a countable discrete group and `tau_U` the
canonical trace on its group von Neumann algebra `L(U)`.  Suppose `L(U)` is
**locally universal**: every separable tracial von Neumann algebra embeds,
unitally and trace-preservingly, into an ultrapower `L(U)^omega` for some
ultrafilter `omega`.  Then `U` is not hyperlinear.

**Definition used.**  "Locally universal" is the notion of Arulseelan--Manzoor,
arXiv:2508.21709, `applications.tex` l.10 (verbatim): "A tracial von Neumann
algebra $\mathcal{S}$ is called \textbf{locally universal} if every separable
tracial von Neumann algebra embeds in an ultrapower of $\mathcal{S}$."  Their
introduction (`intro.tex` l.3) records that the Connes embedding problem asked
exactly whether the hyperfinite factor `R` is locally universal.

**Why it matters.**  It gives a second existence form for
`non-hyperlinear-group`: a single countable group with a locally universal
group factor.  Separable locally universal tracial von Neumann algebras exist
(Arulseelan--Manzoor, `intro.tex` l.20, crediting Farah--Hart--Sherman,
Example 6.4); the open question is whether one of them can be a group factor.
See `some-countable-group-factor-is-locally-universal`.

**Proof.**  Route `locally-universal-group-factor-nonhyperlinear-proof`.  It
uses only the dictionary node, the non-RU constraint system supplied by
`MIP* = RE`, and an elementary moment argument for ultraproducts.

No novelty is claimed: the implication is the observation recorded in the
idea file `research/artifacts/ideas-2026-09-13/nh/nh-model-theory.md`,
approach 4, written out in full.
