---
rg: 2
id: measurable-certificate-routing-preserves-bernoulli-measure
kind: claim
title: An almost-everywhere injective Borel certificate-routing code over any countable group preserves the Bernoulli measure
distinct_from:
  certificate-controlled-routing-is-surjunctive: that proves the topological statement for locally determined routing of bounded displacement, with defects visible on finite patterns; this allows any Borel routing of the whole certificate, unbounded displacement and injectivity only almost everywhere, and concludes preservation of the product measure.
  injective-measure-preserving-ca-is-surjective: that shows a measure-preserving injective automaton is surjective; this shows a routing code that is injective almost everywhere is forced to preserve the measure.
artifacts:
  - research/artifacts/measurable-alphabet-compression-2026-09-12.md
---

Let `G` be a countable group, `C, D` finite alphabets with `|D| >= 2`, and `mu = mu_C x mu_D` the
uniform product measure on `(C x D)^G`. Let `rho: C^G x G -> G` and `pi: C^G x G -> Sym(D)` be Borel,
with `rho_(h.c)(hg) = h rho_c(g)` and `pi_(h.c)(hg) = pi_c(g)`, and put

    tau(c, d) = (c, y),     y(g) = pi_c(g)( d(rho_c(g)) ).

No locality or bounded displacement is assumed. If `tau` is injective on a conull set, then for almost
every `c` the map `rho_c` is a bijection of `G`, and `tau_* mu = mu`.

The proof (Section 2 of the artifact) has three steps:
- mass transport, `E #rho_c^-1(1) = 1`, valid over every countable group;
- Fubini plus a coordinate flip, showing that every site is read;
- in-degree exactly one almost everywhere.

So a routing code never distorts the measure and never lowers Rokhlin entropy, over any group. A
measurable compression must combine several input symbols into one output symbol, or drop certificate
information. Unimodularity is what the proof consumes. On the end-fixing tree of
`end-fixing-tree-symmetries-carry-strict-automata` the transport identity fails, and a routing code
is strict.

**ESTABLISHED 2026-09-12** by [[measurable-certificate-routing-preserves-bernoulli-proof]].
