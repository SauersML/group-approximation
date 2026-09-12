---
rg: 2
id: regular-action-makes-weak-sofic-defects-maximal
kind: claim
title: Left translation sends every nonzero weak-soficity defect to the maximal Hamming defect
distinct_from:
  fixed-separation-hamming-is-not-weak-soficity: that concerns whether a fixed Hamming separation constant can define weak soficity; this computes the Hamming length of the left translation action and draws the consequence for transporting a cellular automaton.
  weakly-sofic-groups-are-surjunctive: that is the open dynamical conclusion; this is the elementary computation that closes one route to it.
artifacts:
  - research/artifacts/weak-soficity-surjunctivity-route-2026-09-12.md
---

Let `H` be a finite group acting on itself by left translation, and let
`l_V(z) = 1 - fix(z)/|H|` be the normalized Hamming length of that action.
Then

```text
l_V(z) = 1   for every z != 1,        l_V(1) = 0.
```

**Consequence.** Let `(H, l, phi)` be a weakly sofic approximation of a group
on a finite symmetric set `F`, and transport an injective cellular automaton
and its local left inverse to `A^H` along left translation, through
`psi(g) = phi(g^-1)` as in Section 1 of the artifact. The defect hypothesis of
the Gromov--Weiss count (`delta < 1` in Proposition 1.2 of the artifact) holds
if and only if every multiplicative defect `phi(a)phi(b)phi(ab)^-1` is trivial.
So through the left regular action the counting argument accepts exactly
local-embedding data, and the bi-invariant length contributes nothing to it.
This does not show that `sigma_H tau_H = id` fails anywhere: the counting
guarantee is only sufficient, and the rules may ignore the moved coordinates.

This is the sharp form of the remark that not every bi-invariant metric on a
finite group restricts from a Hamming metric. The regular action does not
merely lose the metric: it sends every nonzero defect to the largest possible
Hamming defect, so no choice of constants rescues the counting guarantee.

Section 2 of the artifact has the proof and the companion computation for the
conjugation action, where separation is free and near-multiplicativity is
impossible instead.

**Correction 2026-09-12** (gk-vf-positive, Section 8.1 of `research/artifacts/gk-vf-positive-verification-2026-09-12.md`). The computation passes. The consequence overstates. Lemma 1.1 of the artifact gives a *sufficient* condition for the transported identity at a vertex, and a nontrivial defect makes that condition fail at every vertex. What follows is that the defect hypothesis of the Gromov–Weiss count (Proposition 1.2, `delta < 1`) holds iff every defect is trivial. It does not follow that `sigma_H tau_H = id` fails at a positive fraction of vertices, since the rules may ignore the moved coordinates. Read "holds at a positive fraction of vertices only if" as "is guaranteed by the counting argument only if".

Applied 2026-09-12 by gk-free-pos to the Consequence paragraph above.
