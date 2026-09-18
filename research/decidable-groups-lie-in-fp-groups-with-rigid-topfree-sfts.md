---
rg: 2
id: decidable-groups-lie-in-fp-groups-with-rigid-topfree-sfts
kind: claim
title: Every finitely generated group with solvable word problem embeds in a finitely presented group carrying a nonempty minimal topologically free SFT that is quantum rigid
distinct_from:
  decidable-groups-embed-in-fp-groups-with-minimal-free-sft: that is P1, with a free SFT and no rigidity; this asks for rigidity (gate E2) but only topological freeness (gate E1′), which is what the group side of the master route consumes.
  decidable-groups-lie-in-fp-topologically-free-crossed-products: that is the ring-side premise (E′), which also needs torsion-free isotropy and asks only for a finitely presented crossed product; this is the group-side premise, with no isotropy condition.
  rigid-topologically-free-sfts-force-solvable-word-problem: that shows the object asked for here forces a solvable word problem; this asks for it over an overgroup of every decidable group.
---

**OPEN.** Premise E1′ + E2 of `boone-higman-via-v-times-rigid-topfree-sft-full-groups` (lane
bh-g3-topfree, 2026-09-18).

## Statement

For every finitely generated `G` with solvable word problem there are a finitely presented `Λ >= G`
and a nonempty SFT `X ⊆ A^Λ` such that:
- `Λ` acts on `X` minimally and topologically freely;
- `X` is `D`-quantum rigid over every field, for all large `D`.

## Relations

- **Decidability is consumed.** The object forces a solvable word problem on `Λ`
  (`rigid-topologically-free-sfts-force-solvable-word-problem`), so the statement fails for inputs with
  unsolvable word problem, as it must.
- **Known instances.**
  - Subgroups of finite products of tree groups (`free-group-boundary-shifts-are-quantum-rigid`).
  - Cocompact type-rotating Ã₂ lattices and their subgroups
    (`a2-lattice-boundary-skew-shifts-are-quantum-rigid`).
  - Boone–Higman was already known for all of these.
- **Isotropy is unrestricted.** Unlike the ring-side premise, torsion in point stabilizers is allowed.
- **Products add nothing for the input.** For `Λ_0 × F_n` with `X_0 ⊠ X_∂`, each property holds iff it
  holds for `X_0` (`master-route-needs-only-topological-freeness`).

## What is cheaper than the free form, and what is not

- **Cheaper.** Compression codings qualify. The rigid minimal instances recorded in the graph are
  boundary codings, and no free rigid minimal SFT is known over any group.
- **Not cheaper for hard inputs.** Both recorded instances are finite-state Li codings, and these carry
  only inputs whose word problem runs in time `2^(C l^2)`
  (`finite-state-li-coded-full-groups-have-exponential-word-problem`). So for a hard input, `Λ` must
  carry a compression coding that is not finite-state. No such coding is known. Finding one is the
  open core of this premise.

## Lesson for general BH

Relaxing freeness moves boundary codings into the master route. There rigidity and finiteness are
theorems, so the whole existence problem becomes one of carrying the input. Finite-state cone types,
as in tree and building boundaries, are exactly what caps the input. The design target is a rigid
compression coding over an overgroup of the input whose cone-type data is not finite-state.
