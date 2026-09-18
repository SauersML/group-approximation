---
rg: 2
id: contracting-rsgs-closed-under-products-with-finite-groups
kind: claim
title: If H is isomorphic to a contracting rational similarity group and F is finite, then H × F is isomorphic to a contracting rational similarity group
distinct_from:
  free-products-with-a-finite-factor-are-contracting-rsgs: that handles a finite free factor; this handles a finite direct factor.
  non-elementary-hyperbolic-groups-are-contracting-rsgs: that is BBMZ-hyperbolic Question 1.1; this shows that its first obstacle, nontrivial finite normal subgroups, is not an obstruction to being a contracting RSG.
artifacts:
  - research/artifacts/gq-bh-bh-free-23-rsg-q11.md
---

**ESTABLISHED** by `contracting-rsg-finite-product-proof` (lane `bh-free-23`, lane proof,
elementary, not independently reviewed; no priority claimed). It is the special case
`H ≤ H × F` of `contracting-rsgs-closed-under-finite-index-overgroups`.

## Statement

Let `H ≤ R_{Γ,E}` be a contracting RSG (BBMZ arXiv:2309.06224v3, `def:rsg` and
`def:contracting`), and let `F` be a finite group. Then `H × F` is isomorphic to a contracting
RSG `H' ≤ R_{Γ',E'}`, where `Γ'` is `Γ` plus one new root node, `E'` is the cone at that node,
and `Nuc_{H'} = Nuc_H`.

## Consequences

- **Finite normal subgroups are no obstruction.** Contracting RSGs can have nontrivial finite
  normal subgroups, even finite centers. Example: `V_{Γ,E} × Z/2` for any `Γ` with an
  irreducible core. BBMZ list finite normal subgroups as obstacle (i) to their Question 1.1
  (`rmk:horofunction_problems`), because they make the horofunction-boundary action
  unfaithful. The present node shows that obstacle is an artefact of the horofunction model,
  not a property of the class of contracting RSGs.
- **Direct products of hyperbolic groups with finite groups.** For every hyperbolic `G` and
  finite `F, F'`, the groups `(G * Z) × F'` (BBMZ) and `(G * F) × F'` (with `F ≠ 1`, not
  `Z/2 * Z/2`; `free-products-with-a-finite-factor-are-contracting-rsgs`) are isomorphic to
  contracting RSGs. Example: `F_2 × Z/2`.
