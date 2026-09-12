---
rg: 2
id: amenable-envelope-magnus-piece-sofic-proof
kind: route
title: Embed each Magnus truncation into its amenable-edge envelope
target: amenable-envelope-magnus-piece-one-relator-sofic
requires: []
artifacts:
  - research/artifacts/amenable-envelope-magnus-piece-sofic-2026-09-11.md
  - research/artifacts/peelable-extreme-one-relator-sofic-2026-09-11.md
---

Complete written proof in the first artifact. Its literature inputs are the
Freiheitssatz, amalgam and HNN normal forms, Elek--Szabo amalgam permanence
over amenable subgroups, and Ciobanu--Holt--Rees HNN permanence. The kernel
presentation and truncation colimit are §§2 and 4 of the second artifact.

1. Amalgam monotonicity: `A <= A'`, `B <= B'` agreeing on `C` give
   `A *_C B <= A' *_C B'`.
2. Envelope transport: `S *_F B'` is obtained from `S` by the envelope's
   amenable-edge moves, so it is sofic when `S` is.
3. Induction on truncations: `S_j = S_(j-1) *_(F_j) B_j` embeds in
   `S'_(j-1) *_(F_j) B'_j`. The free top Magnus subgroup propagates by the
   Freiheitssatz.
4. Every truncation embeds in a sofic group, so the Magnus kernel is sofic,
   and `G` is sofic because its quotient by the kernel is `Z`.
