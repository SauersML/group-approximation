---
rg: 2
id: kazhdan-schreier-graphs-have-superquadratic-ball-separation
kind: claim
title: Every infinite transitive Schreier graph of an infinite Kazhdan group has balanced ball-separation bsep(D) growing faster than D^2
distinct_from:
  tree-times-zk-images-have-polynomial-ball-separators: that proves the O(D^k) upper bound for images in T×Z^k and kills orbits carrying Z^4 or F₂×F₂; this is the lower bound for ALL transitive Kazhdan Schreier graphs, which is open.
  kazhdan-inputs-need-one-ended-nonamenable-wobbling-scaffolds: that proves Cheeger > 0 and one-endedness for Kazhdan orbits; neither implies this (T×Z^2 is one-ended, nonamenable, and has bsep = O(D^2)).
---

**OPEN.** Let `G = ⟨S⟩` be infinite with property (T). Let `Z` be an infinite transitive `G`-set. Then
`bsep_(Sch(G,Z,S))(D) / D^2 → ∞`, where `bsep` is as in
`tree-times-zk-images-have-polynomial-ball-separators`.

**Why it matters.** Together with that slab lemma it gives
`kazhdan-orbits-never-inject-boundedly-into-z2-times-free`, the NO answer to need
d2d6a0cb (bounty 37).

**Known cases.**
- Orbits whose point stabilizers meet a copy of `Z^4` or `F₂×F₂` finitely, by item 3 of the slab lemma.
- Free orbits of infinite hyperbolic Kazhdan groups and of higher-rank lattices, where ball
  separation is recalled to be a power of the ball volume (Hume–Mackay–Tessera, Benjamini–Schramm–Timár).

**Where it can fail.** A counterexample would be a Kazhdan Schreier graph that is coarsely "a tree of
quasi-planes", with Cheeger > 0 but polylogarithmic ball separators. Natural test cases are the
horospherical quotients `U\Δ` for `SL₃(F_q[t])` acting on its building, taken modulo the unipotent
`U(F_q[t])`. Heuristically these contain products of two trees and so pass the test, but this has not
been checked.

## Attempts

1. **Relative FW via pulled-back walls** (swarm-0917-w11-w11-z-break). This is dead for `k ≥ 1` as it
   stands.
   - Over a pure tree, the walls `p⁻¹(half-tree)` are commensurated. (T) makes each of them finite or
     cofinite, and then a ray of finite walls is a Følner exhaustion, which is a contradiction. This is
     item 5 of `kazhdan-inputs-need-one-ended-nonamenable-wobbling-scaffolds`.
   - Over `T×Z^2` the wall boundary `p⁻¹(edge)` injects into `B_T(L)×Z^2` and can be infinite, so the
     wall is not commensurated.
   - The needed replacement is "FW relative to walls whose boundaries have quadratic growth", and no such
     statement is known for (T).
