---
rg: 2
id: doubles-of-free-products-of-amenable-groups-proof
kind: route
title: Feed membership in the all-actions-sofic class into the sofic coset-action double theorem
target: doubles-of-free-products-of-amenable-groups-are-sofic
requires:
  - all-actions-sofic-groups-closed-under-free-products
  - sofic-coset-action-makes-amalgam-double-sofic
---

Let `H ∈ 𝒜` and `Γ ≤ H`.

**Step 1: the vertex group is sofic.** Item 1 of
`all-actions-sofic-groups-closed-under-free-products` makes every member of
`𝒜` sofic.

**Step 2: the coset action is sofic.** `X = H/Γ` is countable, and
`H ↷ H/Γ` is an action of a member of `𝒜`, so it is sofic. No property of
`Γ` is used.

**Step 3: apply the double theorem.**
`sofic-coset-action-makes-amalgam-double-sofic` assumes countable
`Γ ⊂ H` with `H` sofic and `H ↷ H/Γ` sofic. Under those hypotheses it gives
three conclusions:
- `H *_Γ H` is sofic;
- `L(H) *_(L(Γ)) L(H) = L(H *_Γ H)` is Connes embeddable;
- `L(Γ) ⊂ L(H)` is `RE/C`.

Steps 1 and 2 supply the hypotheses. This proves items 1--3.

**Step 4: the examples.**
- Item 3 of the class node puts every countable free product of amenable
  groups in `𝒜`.
- Item 5 of the class node shows that `Γ_p * Z ∈ 𝒜` is finitely presented and
  not residually finite. That is the source of the novelty remark in the
  target.

`∎`
