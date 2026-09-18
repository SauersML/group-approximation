---
rg: 2
id: automaton-groups-embed-in-lift-presented-automaton-groups
kind: claim
title: Every automaton group embeds in an automaton group whose relator kernel is a finitely generated lift ideal
distinct_from:
  decidable-fg-self-similar-groups-embed-in-fp-self-similar: that asks for a finitely presented self-similar overgroup of any decidable f.g. self-similar group; this asks only for a finite-state overgroup whose Rover–Nekrashevych group is finitely presented, which by Theorem A is a weaker requirement than finite presentation of the overgroup.
  automaton-groups-satisfy-boone-higman: that is the Boone–Higman statement this would imply.
---

**OPEN.** For every automaton group `G <= Aut(X^*)` there are an alphabet `X'` and an automaton group
`G' <= Aut(X'^*)` containing an isomorphic copy of `G` whose relator kernel (for some finite
section-closed generating set) is a finitely generated lift ideal; equivalently, by
`rover-nekrashevych-fp-iff-finite-lift-presentation`, `V_{|X'|}(G')` is finitely presented.

## Remarks

- The lift-ideal condition depends on the action, not only on the group
  (`persistent-automata-rn-group-fp-iff-group-fp`: two actions of `Z/2 ≀ Z` on `T_4`, one with
  `N = K_∞`, one persistent with `K_∞ = 1`). So a natural attack keeps `G` and changes the action, e.g. by
  adding states whose sections kill relators after finitely many splittings.
- The overgroup is residually finite and has word problem in the same space class as `G` (finite-state),
  so neither residual finiteness nor Rauzy's effective-RF invariant obstructs this claim.
- No attempt yet beyond the formulation.
