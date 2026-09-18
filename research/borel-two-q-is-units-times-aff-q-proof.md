---
rg: 2
id: borel-two-q-is-units-times-aff-q-proof
kind: route
title: Split off the scalars of B_2(Q), then use closure of B_A under products and subgroups
target: borel-two-q-is-units-times-aff-q
requires:
  - boone-higman-type-a-class-closed-under-finite-extensions
  - permutational-host-forms-agree-for-countable-inputs
---

**(1).** Every `g = [[a, b], [0, d]]` is `dI` times `[[a/d, b/d], [0, 1]]`. The
scalars `Q^x I` are central, meet `Aff(Q)` trivially (a scalar with lower-right
entry 1 is `I`), and together with `Aff(Q)` generate `B_2(Q)`. So
`B_2(Q) = Q^x I x Aff(Q)`.

**(2).** `B_A` is closed under subgroups and finite direct products
(`boone-higman-type-a-class-closed-under-finite-extensions`), and `Q^x` is
countable abelian, so it lies in `B_A`
(`permutational-host-forms-agree-for-countable-inputs`). If `Aff(Q) ∈ B_A` then
`Q^x x Aff(Q) ∈ B_A`, and members of `B_A` embed in finitely presented simple
groups. Conversely `Aff(Q) <= B_2(Q)`.

**(3).** Write `g in B_(m+1)(Q)` as `[[A, v], [0, d]]` with `A in B_m(Q)`,
`v in Q^m`, `d in Q^x`. Directly,
`[[A, v], [0, d]] = [[I, v d^-1], [0, 1]] · [[A, 0], [0, d]]`, the first factors
form a normal subgroup `≅ Q^m`, the second a complement `≅ B_m(Q) x Q^x`, and
conjugation acts by `v ↦ A v d^-1`.
