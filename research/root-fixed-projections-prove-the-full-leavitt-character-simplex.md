---
rg: 2
id: root-fixed-projections-prove-the-full-leavitt-character-simplex
kind: route
title: Use the common root projection and single-root vanishing to classify the full character
target: binary-leavitt-full-character-simplex
requires:
  - leavitt-root-fixed-projections-equal-the-global-fixed-projection
artifacts:
  - research/artifacts/leavitt-root-projections-and-elementary-character-proof-2026-09-08.md
---

The prerequisite supplies the complete standalone proof. Its common
root fixed projection is central in the represented group algebra,
has trace `a=chi(x_12(1))`, and carries the trivial representation.
On the complementary summand the normalized root trace is zero.
The split row shears, proper-corner orthogonality, and prefix
localization in the same artifact prove that this complementary
character is the canonical regular character. Hence
`chi=a*1+(1-a)*delta_1` on the full group.

Restricting the formula to any subgroup gives the stated necessary
extension criterion, and the ambient mixtures give sufficiency.
If the full group is hyperlinear, scalar blocks together with its
canonical microstates realize every mixture. Thus a nonembeddable
character would prove nonhyperlinearity, but none is constructed.

This route needs no finite-core character theorem or finite-simple-group
character estimate. It connects the already audited elementary proof
to the full-character claim without changing the unresolved
embeddability conclusion.
