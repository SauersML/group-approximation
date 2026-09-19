---
rg: 2
id: stw99-problem-lxxxv-polynomial-growth-invariants
kind: claim
title: Compute the invariant of irreducible-representation quotients for polynomial growth groups (STW Problem LXXXV)
root: true
artifacts:
  - research/artifacts/stw99-final-band-cluster-2026-08-30.md
  - research/artifacts/stw85-integral-heisenberg-invariant-audit-2026-08-31.md
---

**Problem LXXXV of Schafhauser--Tikuisis--White, arXiv:2506.10902.**
Compute `KT_u(C*_π(G))` for infinite-dimensional irreducible
representations `π` of groups `G` of polynomial growth.

## Attempts

* The complete standard integral Heisenberg tower is now computed.
  `stw85-integral-heisenberg-irrep-quotients-are-torus-powers` identifies
  every infinite-dimensional irreducible quotient of
  `H_(2n+1)(Z)` with `A_theta^(tensor n)` for an irrational central
  character, and proves the sharp rational boundary has dimension
  `q^n`.  `stw85-integral-heisenberg-ktu-is-explicit` computes
  `K_0`, `K_1`, the unit, unique trace, full trace pairing, order, and
  coefficient K-groups by the exterior exponential of the block symplectic
  form.  Thus LXXXV is solved for every standard discrete Heisenberg group,
  not merely its three-dimensional first member.
* These quotients are classifiable (polynomial growth ⟹ the
  irreducible quotients are simple with unique trace and finite
  nuclear dimension by Eckhardt--Gillaspy--McKenney-style analysis),
  so the remaining problem is pure computation: `K`-theory of twisted
  noncommutative tori and higher-step nilpotent generalizations.  The
  systematic tool is the same as XXXVII's bottleneck — trace pairings
  via Pimsner--Voiculescu towers along a polycyclic decomposition —
  but here the recursion is finite and explicit: each `C*_π(G)` is an
  iterated twisted crossed product by `Z` of a lower-step quotient,
  so `KT_u` is computable by iterated PV sequences with the pairing
  tracked by the `Λ_τ` formula at each stage.  The honest open issue
  is organizing torsion in the total invariant across stages
  (the `K̲T_u` part), especially for higher-step nilpotent groups.
