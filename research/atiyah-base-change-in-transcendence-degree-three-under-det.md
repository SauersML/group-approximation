---
rg: 2
id: atiyah-base-change-in-transcendence-degree-three-under-det
kind: claim
title: Under the determinant conjecture, Strong Atiyah over Qbar extends to every coefficient field of transcendence degree at most three
distinct_from:
  atiyah-base-change-in-transcendence-degree-two-under-det: that is the established case of transcendence degree at most two; this is degree three, reduced to Philippon's theorem plus the three-variable transcription of the operator side.
  determinant-conjecture-gives-full-atiyah-base-change: that is the statement for all complex coefficients; this is its case of transcendence degree at most three.
---

**OPEN.** Route `atiyah-transcendence-degree-three-via-philippon` reduces it to
one unwritten transcription.

Let `G` be torsion-free and satisfy Strong Atiyah over `Qbar` and Lueck's
determinant conjecture. Then for every field `F ⊂ C` with
`trdeg_(Qbar) F <= 3`, every matrix over `F[G]` has integral von Neumann kernel
dimension, invariant under automorphisms of `C` fixing `Qbar`.

**State of the reduction.**
- **Diophantine input: done.**
  [[points-of-c3-approximable-by-zero-cycles]] (unreviewed) supplies a violating
  Chow form at every point of `C^3`. It comes from Philippon, JNT 81 (2000),
  Theoreme 1 ([[philippon-zero-cycles-approximate-points-of-p3]]).
- **Transcendence degree at most two: done.**
  [[atiyah-base-change-in-transcendence-degree-two-under-det]], reviewed PASS.
- **Missing.** The three-variable versions of Lemmas J and L, the pencil
  reduction, Proposition C with Corollary 6, and the continuity argument of
  Part 4: [[atiyah-cycle-machinery-transcribes-to-three-variables]].

**Beyond degree three.** Transcendence degree `s >= 4` also needs Philippon's
zero-cycle conjecture in dimension `s`
([[philippon-zero-cycle-approximation-conjecture]]). By its author's account
that is blocked by an effective lower bound for arithmetic Hilbert functions.
