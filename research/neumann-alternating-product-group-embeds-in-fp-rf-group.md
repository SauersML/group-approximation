---
rg: 2
id: neumann-alternating-product-group-embeds-in-fp-rf-group
kind: claim
title: B. H. Neumann's two-generated group containing the direct sum of finite odd alternating groups embeds in a finitely presented residually finite group
distinct_from:
  fp-residually-finite-boone-higman: that asks whether finitely presented residually finite groups embed in finitely presented simple groups; this asks whether one explicit residually finite group, with no residually solvable finite-index subgroup, has a finitely presented residually finite overgroup.
artifacts:
  - research/artifacts/gq-bh-openq-lists.md
---

**OPEN.** Asked on MathOverflow by A. Minasyan, question 491978, "A finitely presented
residually finite group that is not virtually residually solvable". It was posted in
2025, and its update of 08 July 2026 was read through the StackExchange API on 2026-09-18.
- **Background:** B. H. Neumann (*Some remarks on infinite groups*, J. London Math.
  Soc. 12 (1937) 120–127) constructed a 2-generated subgroup `G` of the unrestricted
  product `∏_{n≥2} A_{2n+1}` that contains the restricted product `⊕_{n≥2} A_{2n+1}`.
- **Properties:** `G` is residually finite, but no finite-index subgroup of it is
  residually solvable.
- **The question:**

> So, it is natural to wonder, does this group G embed in a finitely presented
> residually finite group?

**Why it is here.** It is a residually finite version of the embedding questions of the
Boone–Higman program. A yes would give a finitely presented residually finite group that
is not virtually residually solvable, which is Minasyan's original aim.

**First constraints.** These are elementary observations, not proved in a node.
- A host must contain `A_m` for unboundedly many `m`. Faithful linear representations of
  `A_m` have degree growing with `m`, so no finitely generated linear group is a host.
- Groups with a uniform bound on the orders of finite subgroups are excluded, for example
  `Aut(F_n)`, mapping class groups and hyperbolic groups.

**Tractability.** Medium. Natural first test: does `⊕_n A_n` alone embed in a finitely
presented residually finite group? It would be enough to find one that contains every
finite group. Compare the RF-host constructions of the gq swarm
(`gq-gq-obstructions-0918-writeup.md`, Part I).
