---
rg: 2
id: finite-block-abelianized-amalgam-proof
kind: route
title: Identify each block and embed its abelianized amalgam into a symmetric double
target: finite-block-mf-quotient-is-abelianized-amalgam
requires:
  - finite-dimensional-kazhdan-fixed-algebra-transport
  - symmetric-double-weak-mf
artifacts:
  - research/artifacts/finite-block-perfect-mf-radicals.md
---

Fixed-algebra transport identifies all copies of any k in one finite block.
Two distinct coordinates commute, so the common image factors through K_ab.
The resulting group is (*_Y K_ab) semidirect V, equivalently
V *_(Gamma+) (Gamma+ x K_ab), by the free-product kernel calculation.

Put D=V x K_ab, which is residually finite. The quotient embeds by reduced
normal forms into D *_(Gamma+) D, which is MF by the second prerequisite.
The universal MF-kernel intersection is therefore exactly ker(q_K).
Section 3 includes the regular-trace C-star argument behind that prerequisite.
