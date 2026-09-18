---
rg: 2
id: cockcroft-2-complexes-over-rn-cd-two-groups-are-aspherical
kind: claim
title: A Cockcroft 2-complex of any size whose fundamental group has cohomological dimension at most 2 and a residually nilpotent augmentation ideal is aspherical
distinct_from:
  finite-2-complex-with-zero-second-l2-betti-is-aspherical: that is an L² criterion for finite 2-complexes; this is an integral criterion (vanishing Hurewicz map) that also applies to infinite 2-complexes.
  locally-indicable-2-complex-with-h2-zero-is-aspherical: that is Howie's theorem and needs H₂ = 0; this needs only the weaker Cockcroft property (no spherical 2-cycles), at the price of cd ≤ 2 and a residually nilpotent augmentation ideal.
  non-proper-power-one-relator-complexes-are-aspherical: that is the one-relator asphericity theorem; this is a general criterion with no bound on the number of relators or generators.
artifacts:
  - research/artifacts/hl-whitehead-bestvina-brady-2026-09-13.md
---

**ESTABLISHED** (proposed; referee requested) through `cockcroft-rn-cd-two-asphericity-proof`.

**Statement.** Let X be a connected CW 2-complex, with any number of cells
(possibly uncountably many). Put G = π₁(X) and let I ⊂ ZG be the augmentation
ideal. Assume:

1. cd G ≤ 2;
2. ⋂ₙ Iⁿ = 0 in ZG;
3. X is **Cockcroft**: the Hurewicz map π₂(X) → H₂(X; Z) is zero.

Then π₂(X) = 0, so X is aspherical.

**When hypothesis 2 holds.**
- It holds for every subgroup of a finitely generated residually torsion-free
  nilpotent group, by Jennings plus a monotonicity step in the proof.
- In particular it holds for every subgroup of a right-angled Artin group,
  including every Bestvina--Brady kernel `H_L`.

**Why this is not Gersten's criterion.** Gersten (arXiv:1501.06875, abstract)
proves the analogue for *finite* 2-complexes with cd π₁ = 2, with no
hypothesis on I. Every 2-dimensional K(`H_L`,1) is infinite, since `H_L` is not
finitely presented, so Gersten's theorem cannot touch it; this claim can.

**Calibration.**
- *cd ≤ 2 cannot be dropped.* The 2-skeleton of the 3-torus has G = Z³, which
  satisfies hypothesis 2. It is Cockcroft, because H₂(X) → H₂(Z³) is an
  isomorphism, but π₂ ≠ 0. The proof fails exactly at step 2, where H₃(G) ≠ 0
  and π₂ ⊗_G Z → H₂(X) is no longer injective.
- *Torsion.* Acyclic presentation complexes of finite perfect groups are
  Cockcroft and not aspherical. Both hypotheses 1 and 2 fail for them
  (I = I² for a perfect group).

**Novelty.** No statement for infinite complexes was found in the graph
(`cairn search` "Cockcroft", "Gersten asphericity") or in a web search. The
ingredients are classical, so a referee should check whether the statement is
folklore.
