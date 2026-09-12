---
rg: 2
id: deligne-lattice-embeds-in-no-rover-nekrashevych-group
kind: claim
title: Deligne's lattice has solvable word problem and embeds in no Rover--Nekrashevych group, so Rover--Nekrashevych commutator hosts are not universal
invalidates:
  - boone-higman-via-rover-nekrashevych-hosts
distinct_from:
  self-similar-hosts-contain-only-residually-finite-groups: that keeps non-residually-finite inputs out of self-similar hosts, with Thompson's V as witness; this keeps a non-residually-finite Kazhdan input out of Rover--Nekrashevych hosts, which do contain V.
  complexity-bounded-host-classes-are-not-universal: that excludes host classes with one recursive word-problem bound; Rover--Nekrashevych hosts have no such bound once H ranges over all self-similar groups, and are excluded here by property (T) instead.
  kazhdan-subgroups-of-rover-nekrashevych-groups-are-rf: that is the general theorem on Kazhdan subgroups of V_d(H); this applies it to one finitely presented decidable input and refutes the universal host claim.
---

**ESTABLISHED.** Let `Gamma~` be the preimage of `Sp_4(Z)` in the universal
cover of `Sp_4(R)`: `deligne-universal-cover-lattice-is-non-rf-kazhdan` with
`n = 2`. Any `n >= 2` works the same way.

1. `Gamma~` is finitely presented and has solvable word problem.
2. `Gamma~` embeds in no `V_d(H)` and no `V_(d,r)(H)`, for any `d >= 2` and any
   self-similar `H <= Aut(T_d)`. In particular it embeds in no
   `[V_d(H),V_d(H)]`, finitely presented or not.

## Consequences

- `decidable-groups-embed-in-rover-nekrashevych-hosts` is false.
- The route `boone-higman-via-rover-nekrashevych-hosts` is dead.
- `boone-higman-conjecture` is untouched: `Gamma~` may still embed in a
  finitely presented simple group of another shape.
- **Binding constraint.** What fails is every Rover--Nekrashevych host, whatever
  `H` is and however hard its word problem. So the complexity condition (R1) of
  the refuted claim is not the binding constraint; property (T) is.
- **Not affected:**
  - the residually finite programme through finitely presented self-similar
    overgroups;
  - hosts whose local maps are not tree automorphisms, such as the finitely
    presented full Cantor groups of
    `fp-full-binary-cantor-groups-have-type-a-actions`.
