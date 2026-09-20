---
rg: 2
id: inverse-diagonal-is-homomorphic-iff-abelian
kind: claim
title: The inverse-diagonal map into a direct square is a homomorphism exactly for abelian groups
invalidates:
  - boone-higman-via-fp-stabilizer-engines
  - boone-higman-via-isolated-stabilizer-engines
artifacts:
  - research/artifacts/boone-higman-cairn-integration-2026-09-20.md
---

For a group G, the map g ↦ (g,g⁻¹) from G to G × G is a group
homomorphism if and only if G is abelian. It is always injective as a set map.

This invalidates the displayed embedding step in the two historical engine
routes, independently of their other obstructions. It does not refute BH.
The pointwise identity (g,g⁻¹) = [(g,1),τ] in the swap extension proves
membership in the derived subgroup, but does not give a homomorphism.

The valid replacement, where a perfect wrapper is suitable, is
`decidable-fp-groups-embed-in-perfect-decidable-fp-groups`. It does not remove
the separate stabilizer-engine finiteness obstruction. No Lean certification
of this new graph node is claimed.
