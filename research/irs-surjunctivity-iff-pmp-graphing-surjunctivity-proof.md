---
rg: 2
id: irs-surjunctivity-iff-pmp-graphing-surjunctivity-proof
kind: route
title: Realize the IRS as a stabilizer process with coset labels, and read colours off extra free-generator loops
target: irs-surjunctivity-iff-pmp-graphing-surjunctivity
requires: []
artifacts:
  - research/artifacts/design-subgroup-tests-2026-09-17.md
---

Complete direct proof: artifact Section 1.

1. **Realization** (Lemma 1.1). Pairs `(H, xi)`, with `xi` an i.i.d. uniform labelling of `H\Gamma`, under the
   action `(H, xi).g = (g^-1 H g, xi(g .))`. The stabilizer is `H` a.s., because a nontrivial normalizer
   element permutes cosets and would force two labels to agree. Shape-dependent tables become measurable tables.
   This gives GG => P1.
2. **Colour lemma.** Add a generator `b_t` for each table pair `t`. It fixes the points of colour `t` and
   rotates an auxiliary circle coordinate irrationally elsewhere.
   - The unique `b`-loop at each vertex reveals the colour.
   - The `Gamma`-components of each orbit are copies of the original coloured orbit.
   - The lifted design acts component by component, so strictness transfers. This gives P1 => GG.
3. **Full-support tables** (Proposition 1.2). Forward-goodness is a condition on a finite pattern of tables that
   holds with probability 1, so it holds on every pattern. Reverse-badness gives a missing image pattern. So
   `(c, x) -> (c, tau_c x)` is a strict automaton over `G`.
