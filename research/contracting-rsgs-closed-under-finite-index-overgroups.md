---
rg: 2
id: contracting-rsgs-closed-under-finite-index-overgroups
kind: claim
title: If a finite-index subgroup of G is isomorphic to a contracting rational similarity group, then so is G
distinct_from:
  contracting-rsgs-closed-under-products-with-finite-groups: that is the special case H ≤ H × F; this is every finite-index overgroup, including non-split extensions such as SL_2(Z) over a free subgroup.
  non-elementary-hyperbolic-groups-are-contracting-rsgs: that is BBMZ-hyperbolic Question 1.1; this closure lemma reduces it to finding one finite-index subgroup in the class.
  virtually-free-product-hyperbolic-groups-are-contracting-rsgs: that is the application to hyperbolic groups with a freely decomposable finite-index subgroup; this is the general closure lemma.
artifacts:
  - research/artifacts/gq-bh-bh-free-23-rsg-q11.md
---

**ESTABLISHED** by `contracting-rsg-finite-index-overgroup-proof` (lane `bh-free-23`, lane proof,
elementary, not independently reviewed; no priority claimed).

## Statement

Let `H ≤ G` have finite index `k`, and suppose `H` is isomorphic to a contracting RSG
`H ≤ R_{Γ,E}` (BBMZ arXiv:2309.06224v3, `def:rsg`, `def:contracting`). Then `G` is isomorphic to
a contracting RSG `G' ≤ R_{Γ',E'}`, where:
- `Γ'` is `Γ` plus one new root node;
- `E'` is the union of `k` labelled copies of `E`;
- `Nuc_{G'} ⊆ Nuc_H`.

The `G`-action is the induced action `G ×_H E`.

## Consequences

- The class of groups isomorphic to contracting RSGs is closed under finite-index overgroups.
  For BBMZ-hyperbolic Question 1.1 it therefore suffices to find one finite-index subgroup in
  the class.
- The finite-product lemma `contracting-rsgs-closed-under-products-with-finite-groups` is the
  special case `H ≤ H × F`.
- Applied to free subgroups: `virtually-free-product-hyperbolic-groups-are-contracting-rsgs`,
  for example `SL_2(Z)`.
