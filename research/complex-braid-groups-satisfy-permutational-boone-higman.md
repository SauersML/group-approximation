---
rg: 2
id: complex-braid-groups-satisfy-permutational-boone-higman
kind: claim
title: The braid group of every finite complex reflection group lies in B_A (open only for G_24, G_27, G_29, G_33, G_34)
distinct_from:
  complex-braid-groups-in-pbh-except-g24-g27-g29-g33-g34: that is the established part, every type but five; this is the full statement, open exactly at those five.
  artin-groups-satisfy-boone-higman: that is the real, infinite-type-allowed Artin problem; this is the finite complex reflection problem, whose real part is the spherical Artin groups.
artifacts:
  - research/artifacts/gq-bh-bh-verify-artin-euclidean-toric.md
---

**OPEN.** For every finite complex reflection group `W`, the braid group
`B(W) = π_1(W\V^reg)` lies in `B_A`, and so embeds in a finitely presented simple
group.

**Established part:** `complex-braid-groups-in-pbh-except-g24-g27-g29-g33-g34`. Every
type is settled except the five exceptional well-generated groups `G_24`, `G_27`,
`G_29`, `G_33`, `G_34`. These are exactly the cases for which no fibration of
`V^reg` was known, so that their K(π,1) property waited for Bessis's Garside-theoretic
proof (arXiv:math/0610777v4, Introduction, p. 2, read).

## What is known about the five

- **Linearity.** Not known. Marin constructs generalized Krammer representations and
  conjectures faithfulness (J. Algebra 2012; abstract only). If they are faithful, all
  five follow from `finitely-generated-linear-groups-satisfy-boone-higman`.
- **Garside structure.** All five are well-generated, so `B(W)` is a Garside group
  (Bessis's dual braid monoid). Boone--Higman for Garside groups is not known on
  main; compare `automatic-groups-satisfy-boone-higman` (open).
- **Not regular centralizers of real groups.** By Springer's degree count, none of
  the five has as its degrees the degrees divisible by `d` of a real group of type
  E, F, H, A, B or D. That count rules out the route used for `G_31`.
- **Rank three (`G_24`, `G_27`).** `V^reg ≅ C^× × (P^2 − A)`, where `A` is the
  projectivized mirror arrangement: Klein's 21 lines for `G_24`, Valentiner's 45 lines
  for `G_27`. So `P(W) ≅ Z × π_1(P^2 − A)`, and the question is whether these two
  line-arrangement groups lie in `B_A`.
  - Calibration: for the Hessian group `G_25`, the Hesse pencil fibres
    `P^2 − (12 lines)` over `P^1 − 4 points` with fibre a smooth cubic minus 9 points.
    No pencil with this property is known for the Klein or Valentiner arrangements.
- **Lyashko--Looijenga.** For well-generated `W`, the projection `W\V^reg -> Y`
  forgetting the top invariant is an `F_n`-fibration over `Y − K` (`K` the bifurcation
  locus). `Y − K` finitely covers the centred `Conf_n(C)/S_n` (Bessis, p. 4). So
  `π_1(p^-1(Y − K))` is `F_n`-by-(finite index in `B_n`), which lies in `B_A`. But
  `p^-1(Y − K)` is `W\V^reg` minus the divisor `p^-1(K)`, so `B(W)` is only a
  quotient of it. The same "filling" obstruction appears for D̃_n
  (`d-tilde-artin-groups-satisfy-permutational-boone-higman`).
- **Possible reduction (cited, not used).** `G_33` is a parabolic subgroup of `G_34`,
  and braid groups of parabolic subgroups embed in `B(W)` (BMR). If so,
  `B(G_33) ≤ B(G_34)`, and it suffices to treat `G_24`, `G_27`, `G_29`, `G_34`.
