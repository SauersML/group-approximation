---
rg: 2
id: arbitrarily-complex-fp-simple-via-transcendental-slope-thompson
kind: route
title: Finitely presented simple hosts of the Liouville-slope Thompson groups D(V_λ) inherit their arbitrarily hard word problems
target: fp-simple-groups-with-arbitrarily-complex-word-problem
requires: [transcendental-slope-thompson-groups-satisfy-boone-higman, transcendental-slope-thompson-groups-have-hard-word-problems]
---

Fix a recursive `T` and put `T^+(m) = m + max_(k<=m) T(k)`.

1. **A hard input.** `transcendental-slope-thompson-groups-have-hard-word-problems`, item 2, applied to
   `T^+`, gives a computable Liouville `λ` such that the 2-generated simple group `D(V_λ)` has solvable
   word problem that is not `T^+`-bounded. It is decided by the Sturmian detector
   `[u', ρ^n w' ρ^{-n}]` of item 1.
2. **The host.** `transcendental-slope-thompson-groups-satisfy-boone-higman` embeds `D(V_λ)` in a
   finitely presented simple group `G`.
3. **Transfer.** Item 3 of the first node: a `T^+`-bounded word problem for `G` restricts, by
   length-linear substitution, to one for `D(V_λ)`, contradicting step 1.

So `G` beats `T`. ∎ (Lane proofs; see the required nodes for status. The first premise is OPEN, and
this route shows it is at least as strong as the target for the λ of step 1.)
