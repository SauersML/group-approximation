---
rg: 2
id: one-relator-soficity-localizes-at-rational-derived-stage-proof
kind: route
title: Localize soficity at the finite rational-derived stage by a quotient-compatibility lemma
target: one-relator-soficity-localizes-at-rational-derived-stage
requires: [linton-rational-derived-series-theorem]
artifacts:
  - research/artifacts/one-relator-soficity-audit-2026-08-17.md
---

## Direct proof

The full argument is written out in the claim.  Its three moves, and why the
route is a genuine step rather than a restatement of its single prerequisite:

1. **Solvability of `G/E`** uses only that the rational derived series is
   characteristic with torsion-free abelian factors.  No input from the
   prerequisite.
2. **`E/R` free** is where the prerequisite enters, and not by quotation.
   Corollary 1.2(2) applies to *residually rationally solvable* one-relator
   groups, and `G` is not assumed to be one.  The step is to apply it to
   `G/R = F/<<r>>` — which is one-relator, with relator `r`, and residually
   rationally solvable by the same corollary — and then transport the
   conclusion back along a lemma proved here: if `R ⊆ A_Q^(ω)` then
   `(A/R)_Q^(i) = A_Q^(i)/R`, because `A_Q^(i)/A_Q^(i+1)` is torsion-free.  That
   lemma is not in the source.
3. **The equivalence** uses subgroup permanence in one direction and
   Elek--Szabó (sofic kernel, amenable quotient) in the other.  Neither is in
   the prerequisite, and the second is what makes the claim about soficity at
   all — the prerequisite has no approximation content whatsoever.

So the prerequisite supplies the group theory and this route supplies the
transport lemma and the approximation theory.
