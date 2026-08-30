---
rg: 2
id: stw99-problem-lxxxv-polynomial-growth-invariants
kind: claim
title: Compute the invariant of irreducible-representation quotients for polynomial growth groups (STW Problem LXXXV)
root: true
artifacts:
  - research/artifacts/stw99-final-band-cluster-2026-08-30.md
---

**Problem LXXXV of Schafhauser--Tikuisis--White, arXiv:2506.10902.**
Compute `KT_u(C*_π(G))` for infinite-dimensional irreducible
representations `π` of groups `G` of polynomial growth.

## Attempts

* These quotients are classifiable (polynomial growth ⟹ the
  irreducible quotients are simple with unique trace and finite
  nuclear dimension by Eckhardt--Gillaspy--McKenney-style analysis),
  so the problem is pure computation: `K`-theory of twisted
  noncommutative tori and their nilpotent generalizations.  The
  systematic tool is the same as XXXVII's bottleneck — trace pairings
  via Pimsner--Voiculescu towers along a polycyclic decomposition —
  but here the recursion is finite and explicit: each `C*_π(G)` is an
  iterated twisted crossed product by `Z` of a lower-step quotient,
  so `KT_u` is computable by iterated PV sequences with the pairing
  tracked by the `Λ_τ` formula at each stage.  The honest open issue
  is only organizing torsion in the total invariant across stages
  (the `K̲T_u` part); recorded as a finite-per-group computation
  rather than a conceptual problem, ripe for a systematic paper on
  step ≤ 3 nilpotent groups where all invariants would be tabulated.
