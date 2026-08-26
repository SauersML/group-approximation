---
rg: 2
id: literal-sofic-assembly
kind: claim
title: The literal finitely presented non-MF group is sofic, assembled hypothesis-free in Lean
artifacts:
  - GroupApproximation/Sofic/LiteralSoficAssembly.lean
distinct_from:
  literal-group-sofic: that is the mathematical statement that the literal group is sofic, with its notes-level proof; this records the kernel-checked assembly `LiteralSoficAssembly.markedGroup_isSofic`, which joins the block-Clifford tower theorem to the literal normal form through the vertical-group identification, with no hypothesis and no literature input.
  finitely-presented-sofic-non-mf: that packages soficity with finite presentation and failure of MF; this is only the soficity half, as a Lean declaration usable by compilers.
---

ESTABLISHED, kernel-checked: `Sofic/LiteralSoficAssembly.markedGroup_isSofic :
IsSofic MarkedGroup`, with no hypothesis.  It composes
`BlockCliffordTowerSofic.isSofic_blockClifford_tower` (residually finite
base, injective compression, finite level orbits) with the literal block
normal form `E ~= C(G) x| Vertical` through `LiteralVerticalBridge`, which
identifies the two vertical groups.  This is the declaration the sofic
promise compiler [[sofic-promise-mf-recognition-two-isomorphism-types]]
consumes.
