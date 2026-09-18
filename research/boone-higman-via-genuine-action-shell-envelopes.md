---
rg: 2
id: boone-higman-via-genuine-action-shell-envelopes
kind: route
title: Present a genuine-action shell envelope of an overgroup and apply the twisted Brin–Thompson criterion
target: boone-higman-conjecture
requires:
  - decidable-inputs-have-fp-genuine-action-shell-envelopes
  - genuine-action-shell-envelopes-generalize-the-regular-shell
  - twisted-brin-thompson-finite-presentation-criterion
artifacts:
  - research/artifacts/gq-bh-shell-universal-genuine-actions.md
---

Let `G` be finitely generated with decidable word problem. The OPEN claim supplies
`P >= G` and an action `rho` with infinite supports such that `E_rho` is finitely presented.
By item 1 of the generalization claim, `P`, and so `G`, embeds in `E_rho`. By item 4 the finite
point stabilizers of `E_rho` on the dense orbit `Omega` are finitely generated, and `E_rho`
is highly transitive on `Omega` because it contains `V`. The twisted Brin–Thompson criterion
gives a finitely presented simple group containing `E_rho`, hence `G`.

This is the route `boone-higman-via-fp-shell-envelopes` with the regular enumeration
replaced by an arbitrary genuine action with infinite supports. Its only open input is the
finite presentation of `E_rho`.
