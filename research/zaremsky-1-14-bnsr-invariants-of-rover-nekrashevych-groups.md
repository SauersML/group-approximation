---
rg: 2
id: zaremsky-1-14-bnsr-invariants-of-rover-nekrashevych-groups
kind: claim
title: "Zaremsky Problem 1.14 resolved: compute the BNSR invariants of Rover--Nekrashevych groups"
root: true
distinct_from:
  rover-nekrashevych-finite-presentation-criteria: that records when V_d(H) and its commutator subgroup are finitely presented, the simplicity of the commutator subgroup and the abelianization formula; this asks for the BNSR invariants Sigma^m of V_d(H) on its character sphere.
---

M. C. B. Zaremsky, *Some open problems* (version of July 12, 2026,
https://zaremsky.github.io/open_problems.pdf), Section 1, Problem 14, verbatim:
"Compute the BNSR-invariants of Röver–Nekrashevych groups."

This claim is the question. It is established only through an answer route:

- **Computation**: `zaremsky-1-14-by-computation` requires
  `rover-nekrashevych-bnsr-invariants-are-full`, the current candidate answer.
  If that candidate fails for some group, a different explicit computation claim
  replaces it; the route is then rewired to that claim.

Never write a `requires: []` route into this claim.

## Precise reading

- `X = {1,...,d}` with `d >= 2`, `T_d = X^*`, `C = X^N`. A group `G <= Aut(T_d)`
  is self-similar when every section `g|_x` lies in `G`. The action is faithful.
- The Röver–Nekrashevych group `V_d(G)` is the group of homeomorphisms `h` of `C`
  with cone partitions `C = u_1 C ⊔ ... ⊔ u_k C = v_1 C ⊔ ... ⊔ v_k C` and
  `g_1,...,g_k in G` such that `h(u_i w) = v_i g_i(w)` (definition as in
  `rover-nekrashevych-groups-are-highly-transitive`).
- `S(Γ) = (Hom(Γ,R) \ {0}) / R_{>0}` is the character sphere, and
  `Σ^m(Γ) ⊆ S(Γ)` is the homotopical Bieri–Neumann–Strebel–Renz invariant,
  defined when `Γ` has type `F_m` (`Σ^1` needs only finite generation).
- **What counts as an answer.** For every finitely generated self-similar `G`:
  an explicit description of `S(V_d(G))` in terms of `G`, and of `Σ^m(V_d(G))`
  for every `m` for which `V_d(G)` has type `F_m`. A computation for a subclass
  (for example `G` of type `F_∞`, or contracting `G`) is partial progress.
- **Where the question has content.** The sphere is empty when `V_d(G)` has finite
  abelianization. That happens for the Higman–Thompson groups `V_d` and for Röver's
  group `V_2(Grigorchuk group)`, whose generators are involutions. By Nekrashevych's
  abelianization formula (item (Ab) of `rover-nekrashevych-finite-presentation-criteria`)
  the real characters of `V_d(G)` are exactly the characters `χ` of `G` with
  `χ(g) = Σ_x χ(g|_x)`. So the question has content exactly for self-similar
  groups with such a nonzero character, for example the binary odometer.

## Attempts

- 2026-09-13 (lane z1-14-rover-nek): the character sphere is the sphere of
  sum-invariant characters of `G`, and `Σ^1(V_d(G))` is the whole sphere for every
  finitely generated self-similar `G`. The argument uses small-support living
  elements that commute with every generator. The higher invariants are open. The
  proposed route is Morse theory on the Stein–Farley complex, whose cell stabilizers
  meet `ker χ` in products of kernels. Details are in
  `rover-nekrashevych-bnsr-invariants-are-full`.
