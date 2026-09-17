---
rg: 2
id: kazhdan-host-route-imports-have-verbatim-sources
kind: claim
title: The property-A-to-amenable-compact-model import and the (T)-plus-Haagerup finiteness import of the Kazhdan host route have verbatim sources matching their use
distinct_from:
  stw40-unital-nuclear-no-trace-iff-exact: that states the equivalence of exactness with an amenable compact metrizable model, supported by one sentence and "the usual Stone--Cech proof" and without a definition of exact; this asks for a quoted source for property A implies an amenable action, with the definitions matched to property A as the host route supplies it, plus a metrizable (R1) model.
  thompson-v-has-haagerup-property: that records the Haagerup property of V without verbatim source text; this asks only for a quoted source that a countable group with property (T) and the Haagerup property is finite.
  amenable-purely-infinite-groupoid-full-group-hosts-kazhdan: that is the groupoid example; this is the citation gap a referee found in its proof route.
---

**ESTABLISHED by citation route `kazhdan-host-route-imports-citation`** (referee ref-03,
2026-09-17). This was the citation gap found at audit (2026-09-17) in the route
`amenable-purely-infinite-groupoid-kazhdan-host-proof`. The mathematics of that route
was checked and holds; what was missing is source text for two imports.

**Claim.** Both of the following are supported by verbatim citations whose hypotheses
match the use made of them in the host route.

1. **Property A implies an amenable compact metrizable model.** If a countable discrete
   group `Γ` has Yu's property A, then `Γ` admits a continuous action on a compact
   metrizable space `Y` with continuous `ν_n: Y → Prob(Γ)` such that
   `sup_y ||γν_n(y) − ν_n(γy)||_1 → 0` for every `γ` (form (R1)). The source must state
   the notions it uses, and they must match what the route supplies for
   `Γ = Z^3 ⋊ SL_3(Z)` (property A via Guentner–Tessera–Yu).
   *Referee note (ref-03):* the audit version phrased the hypothesis as "exact reduced
   C*-algebra (equivalently, Yu's property A)". The host route only ever supplies
   property A, so the hypothesis is stated as property A. That avoids the
   exactness-to-property-A equivalence altogether. The route imports Higson–Roe's
   theorem (property A iff an amenable action on a compact Hausdorff space), quoted
   from Willett's notes, and proves the metrizable (R1) upgrade in full.
2. **(T) plus Haagerup is finite.** A countable group with property (T) and the Haagerup
   property is finite. The Haagerup property also passes to subgroups. The source is
   Chatterji–Druţu–Haglund, Theorem `THker` (Delorme–Guichardet, Akemann–Walter), quoted
   verbatim in the route.
