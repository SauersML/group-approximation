---
rg: 2
id: gl-n-q-all-n-in-st-10-of-resolvent-ring
kind: route
title: One finitely presented Kazhdan group St_10(R_L) contains GL_n(Q) for every n
target: gl-n-q-explicit-natural-fp-overgroup
requires:
  - leavitt-pair-centralizers-embed-e-n-in-st-3n-plus-1
  - leavitt-resolvent-ring-is-fp-and-contains-q
  - steinberg-groups-of-fp-rings-are-fp-in-rank-five
artifacts:
  - research/artifacts/gq-steinberg-q-krstic-mccool-source.md
---

Put `Γ = St_10(R_L)`, where `R_L` is the ring of
`leavitt-resolvent-ring-is-fp-and-contains-q`.

- **Finitely presented.** `Γ` is finitely presented with an explicit presentation, since
  `10 >= 5` (`steinberg-groups-of-fp-rings-are-fp-in-rank-five`, refereed by a and b).
  Property (T) comes from `steinberg-finite-presentation-and-kazhdan-theorem`; it is not
  needed for the target.
- **Contains every GL_n(Q).** `Q ⊆ R_L`, and `R_L` carries a Leavitt pair. So part 2 of
  `leavitt-pair-centralizers-embed-e-n-in-st-3n-plus-1` puts every `GL_n(Q)` into `Γ`.
- **Presentation.** Fully explicit: the rank-five node's presentation of `St_10(F_6)` (630
  generators; relation families (B1), (B2)), plus the nine relator words. As in
  `gl-n-q-explicit-via-steinberg-group-of-resolvent-ring`:
  `Γ = St_10(F_6)/⟨⟨x_12(ρ_1), …, x_12(ρ_9)⟩⟩`, with the nine relator words written there
  (`st-n-of-ring-quotient-adds-one-relator-per-ideal-generator`).

This improves the rank-`(6n+7)` route in two ways: there is one group for all `n`, and a
fixed rank of 10. It is not simple.
