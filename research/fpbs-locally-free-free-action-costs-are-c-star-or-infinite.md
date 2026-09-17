---
rg: 2
id: fpbs-locally-free-free-action-costs-are-c-star-or-infinite
kind: claim
title: Every free action of a countable locally free group has cost c* or infinity, and pseudocost at most c*
distinct_from:
  fpbs-fixed-price-non-amenably-generated-from-fg: that is the conditional passage for all groups outside the amenably generated class; this is an unconditional cost dichotomy for locally free groups, which excludes shape (A) of Theorem G there but does not decide fixed price.
artifacts:
  - research/artifacts/fpbs-locally-free-fixed-pseudocost-2026-09-17.md
---

**ESTABLISHED** through `fpbs-locally-free-free-action-costs-are-c-star-or-infinite-proof`.

Let `Γ` be a countably infinite locally free group, and let `c*(Γ)` be as in
`locally-free-groups-first-l2-betti-equals-c-star-minus-one`. Every free
p.m.p. action `a` of `Γ` satisfies

```text
C(a) ∈ { c*(Γ), ∞ }      and      PC(a) ≤ c*(Γ).
```

If some free action has finite cost, then `C(Γ) = c*(Γ)` and every free action
has pseudocost exactly `c*(Γ)`. So:
- `Γ` has fixed price iff it does not have both a free action of finite cost
  and one of infinite cost.
- This needs no hypothesis on finitely generated groups.
- In Theorem G of `research/artifacts/fpbs/docs/fixed-price-countable-passage.md`,
  a locally free counterexample has shape (B), never shape (A). Its
  infinite-cost free action gives a positive answer to Tucker-Drob's Q 7.6.
- Condition (L) of Theorem E holds for all locally free groups.
- For the test group `Γ_mal` of this hole's attempts, every free action has
  cost 2 or ∞.

Artifact: `research/artifacts/fpbs-locally-free-fixed-pseudocost-2026-09-17.md`, §5.
