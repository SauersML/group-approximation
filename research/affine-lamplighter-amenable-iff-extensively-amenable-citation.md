---
rg: 2
id: affine-lamplighter-amenable-iff-extensively-amenable-citation
kind: route
title: Import of Juschenko–Monod Lemma 3.1 and of the definition and Lemma 2.1 of Juschenko–Matte Bon–Monod–de la Salle
target: affine-lamplighter-amenable-iff-extensively-amenable
requires: []
---

**Sources.**
- K. Juschenko and N. Monod, *Cantor systems, piecewise translations and simple amenable groups*,
  arXiv:1204.2132; Ann. of Math. 178 (2013) 775–787.
- K. Juschenko, N. Matte Bon, N. Monod and M. de la Salle, *Extensive amenability and an application to
  interval exchanges*, arXiv:1503.04977; Ergodic Theory Dynam. Systems 38 (2018) 195–219.

**How they were read.** Both arXiv PDFs were fetched on 2026-09-14 and their text extracted locally with
`pdftotext -layout`. The journal versions were not compared.

**Verbatim (Juschenko–Monod, §3).** "Lemma 3.1. Assume that G acts transitively on X and choose x0 ∈ X. The
following assertions are equivalent." Among them: "(ii) The P_f(X) ⋊ G-action on P_f(X) admits an
invariant mean." and "(iv) The G-action on P_f(X) admits an invariant mean giving full weight to the
collection of sets containing x0."

**Verbatim (Juschenko–Matte Bon–Monod–de la Salle).**
- "Definition 1.1. The action of a group G on a set X is extensively amenable if there is a G-invariant mean
  on P_f(X) giving full weight to the collection of subsets that contain any given element of P_f(X)."
- "Lemma 2.1. Every action of an amenable group is extensively amenable, and every extensively amenable
  action on a nonempty set is amenable."
- Introduction: "it was shown in [JM13, 3.1] that the amenability of this affine action is equivalent to the
  extensive amenability of G y X."

**Matching the claim.** Definition 1.1 implies (iv) for any `x0`. Conversely, the proof of (iii)⇒(iv) in
Lemma 3.1 (unions of independent sets) upgrades full weight at one point to full weight at any finite set.
So (iv) is equivalent to Definition 1.1 for transitive actions. JMBMdlS Lemma 2.2 (iv)⇔(i) states this.
