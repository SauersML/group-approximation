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
