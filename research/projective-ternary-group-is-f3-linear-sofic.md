---
rg: 2
id: projective-ternary-group-is-f3-linear-sofic
kind: claim
title: The ternary Leavitt unit group modulo scalars is linear sofic over F_3
distinct_from:
  binary-leavitt-unit-group-is-f2-linear-sofic: that is F_2-linear soficity of the binary unit group, the gate of the binary Kaplansky lane; this is F_3-linear soficity of the ternary scalar quotient, the gate of the ternary invariant-output lane.
  projective-leavitt-unit-groups-mod-scalars-are-nonsofic: that is the established failure of Hamming approximation for the same group; this is the rank-metric approximation property, which nonsoficity does not exclude.
artifacts:
  - research/artifacts/invariant-output-descent-and-sensitivity-2026-09-12.md
---

**OPEN.** `PG = L_(F_3)(1,2)^x / {±1}` is linear sofic over `F_3` in the sense of
Arzhantseva--Paunescu.

**Payoff.** `F_3[PG]` is then stably finite (`linear-sofic-group-algebra-is-stably-finite`),
so `projective-ternary-swap-idempotent-is-not-full` holds
(`f3-linear-soficity-refutes-projective-swap-fullness`). The swap-invariant linear
architecture and its Klein strengthening both die, and every injective `F_3`-linear
automaton over `PG` is surjective. Through the corner embedding the unit group
`L_(F_3)(1,2)^x` is then `F_3`-linear sofic too. So its group algebra
`S_+ x S_-` is stably finite, and the anti-central half
`ternary-anti-invariant-swap-corner-is-full` dies as well. Either half, padded by
the unit of the other factor, would be a direct-finiteness failure there. In the other direction, fullness of the swap
idempotent refutes this claim (`non-linear-sofic-via-projective-ternary-swap-fullness`).

## Attempts

- *Through soficity.* Dead: `PG` is nonsofic
  (`projective-leavitt-unit-groups-mod-scalars-are-nonsofic`).
- *Subgroups.* Linear soficity passes to subgroups, so this claim would make
  `L_(F_3)(1,2)^x` linear sofic over `F_3`, through the corner embedding
  (`leavitt-units-embed-in-their-scalar-quotient`). The converse would need linear
  soficity to pass to the quotient by the finite centre. No such permanence is
  recorded, and it is not attempted here.
- *The shared question.* Deciding this is the rank-metric question the binary gate
  `binary-leavitt-unit-group-is-f2-linear-sofic` asks over `F_2`: whether
  almost-representations of the Kazhdan subgroups in normalized rank can be rounded.
  Nothing here decides it over either field.
- *Property (T) does not round rank models over finite fields.* By
  `kazhdan-group-rank-models-admit-no-expander-decomposition` (gk-kdf-structure), exact
  rank models of `EL_3(F_p[t])` over any finite field admit no decomposition into
  expanding pieces. So a proof that `PG` is not `F_3`-linear sofic cannot copy the
  Hamming proof's step where (T) rounds the models of the Kazhdan subgroup. This does
  not decide the gate. `PG` has no nontrivial finite-dimensional representations, and
  perturbed models with sublinear pieces are not covered.
- *Module-type models.* Dead at every block dimension (gk-l-gate-pos). Restricted to
  `EL_3` of the ternary Leavitt algebra, which sits inside `PG` through the corner
  embedding, a model whose root subgroups act by block unipotents between blocks of
  arbitrary ranks is trivial (`block-unipotent-rank-models-of-leavitt-el3-are-trivial`).
  The Steinberg triples produce a unital corner homomorphism of `L_(F_3)(1,2)`, and direct
  finiteness of rank-ultraproduct corners kills it.
- *Permutation-type models.* Dead. Monomial rank models over `F_3` are Hamming models up
  to a factor two (`monomial-rank-models-are-hamming-models`), and `PG` is nonsofic. The
  remaining class is recorded in Section 7 of
  `research/artifacts/leavitt-unit-rank-model-construction-audit-2026-09-12.md`.
