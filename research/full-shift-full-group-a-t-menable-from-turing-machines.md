---
rg: 2
id: full-shift-full-group-a-t-menable-from-turing-machines
kind: route
title: "Haagerup for RTM(2,1) = M_2 restricts to the full-shift topological full group"
target: full-shift-topological-full-group-is-a-t-menable
requires:
  - reversible-turing-machine-groups-are-a-t-menable
  - lebesgue-preserving-subgroup-of-2v-is-the-turing-machine-group
  - nv-cocycle-kernel-is-jacobian-kernel-meet-diagonal
---

By item 3(c) of `nv-cocycle-kernel-is-jacobian-kernel-meet-diagonal`, `Φ^{-1} [[X]] Φ ≤ M_2`.
By item 1 of `lebesgue-preserving-subgroup-of-2v-is-the-turing-machine-group`, `M_2 ≅ RTM(2, 1)`.
A proper cnd function on `RTM(2, 1)` (`reversible-turing-machine-groups-are-a-t-menable`)
transports to `M_2` and restricts to a proper cnd function on `[[X]]`.

**Use.** This is the middle link of the chain
`brin-thompson-groups-nv-are-a-t-menable ⟹ reversible-turing-machine-groups-are-a-t-menable ⟹
full-shift-topological-full-group-is-a-t-menable`. It is a sufficient route for the last claim that
does not pass through all of `2V`. Its hypothesis admits no cubical proof, but the conclusion might
still have one (item 4 of the identification node: `[[X]]` has no distorted element).
