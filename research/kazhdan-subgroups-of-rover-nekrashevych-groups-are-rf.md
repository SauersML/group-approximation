---
rg: 2
id: kazhdan-subgroups-of-rover-nekrashevych-groups-are-rf
kind: claim
title: Kazhdan subgroups of Rover--Nekrashevych groups virtually embed in finite powers of the self-similar group, so they are residually finite
distinct_from:
  thompson-v-has-haagerup-property: that is Farley's proper affine action of V itself, which makes every Kazhdan subgroup of V finite; this treats V_d(H) for an arbitrary self-similar H, where Kazhdan subgroups can be infinite, and proves that they virtually embed in a finite power of H.
  self-similar-hosts-contain-only-residually-finite-groups: that shows every subgroup of a self-similar group is residually finite; this shows that the Rover--Nekrashevych overgroup, which contains V and is not residually finite, adds no non-residually-finite subgroup with property (T).
  rover-nekrashevych-word-problem-reduces-to-self-similar-group: that bounds the word problem of V_d(H) by that of H; this restricts which groups with property (T) embed in V_d(H) at all, whatever the complexity of H.
---

**ESTABLISHED.** Let `d >= 2`, let `H <= Aut(T_d)` be self-similar, and let
`V_d(H)` be its Rover--Nekrashevych group acting on `X^omega`,
`X = {0,...,d-1}`. Let `G <= V_d(H)` have property (T), or more generally
property FW: every commensurated subset of every `G`-set is transfixed. Then
some finite-index subgroup `G_0 <= G` embeds in `H^n` for some `n`. In
particular `G` is residually finite.

The proof is the route
`kazhdan-subgroups-of-rover-nekrashevych-groups-are-rf-proof`. It applies
verbatim to the multi-root groups `V_(d,r)(H)`, and so also to every subgroup,
including `[V_d(H),V_d(H)]`.

## Consequences

- No non-residually-finite group with property (T), in particular no infinite
  simple Kazhdan group, embeds in any `V_d(H)`.
- For trivial `H` the proof gives that Kazhdan subgroups of `V_d` are finite.
  For `d = 2` that agrees with `thompson-v-has-haagerup-property`.
- `deligne-lattice-embeds-in-no-rover-nekrashevych-group` applies it to a
  finitely presented decidable input and refutes
  `decidable-groups-embed-in-rover-nekrashevych-hosts`.

## Scope

The proof uses that the local maps of `V_d(H)` form a group of tree
automorphisms, which is residually finite. It says nothing about full groups
whose local maps are general homeomorphisms or rational transducers, such as
rational similarity groups, or the finitely presented full Cantor groups of
`fp-full-binary-cantor-groups-have-type-a-actions`.
