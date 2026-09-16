---
rg: 2
id: residually-finite-group-not-stable-in-finite-actions
kind: claim
title: Some residually finite group is not stable in finite actions
distinct_from:
  literal-group-not-stable-in-finite-actions: that group is not residually finite, and its instability is forced by soficity; this asks for a residually finite example, where that mechanism gives nothing
  alekseev-thom-stability-finite-actions-boundary: that records that this question is open, together with residual amplification and the normal-kernel boundary; this is the question itself as a claim
  hyperbolic-rf-not-flexibly-p-stable: that is failure of flexible P-stability, which implies stability in finite actions and already fails for F2 x Z; this asks for failure of the weaker property
  f2xf2-not-stable-in-finite-actions: that fixes the group F2 x F2; this is existential over residually finite groups
---

**OPEN.** There is a residually finite group that is not stable in finite actions (Gohla--Thom
Definition 3.7). This is Gohla--Thom Question 3.12 (arXiv:2403.09582v2), quoted in
`research/artifacts/f2xf2-finite-action-stability-dichotomy-2026-09-16.md` §0.2. Alekseev--Thom
(arXiv:2512.15494v1, introduction) record it as open.

## Attempts

* **Hyperbolic groups.** Alekseev--Thom Corollary C: "There exists a hyperbolic group that cannot be stable
  in finite actions, provided it is residually finite." Dies at residual finiteness of hyperbolic groups,
  which is open.
* **Sofic non-residually-finite groups.** Sofic plus stable forces residual finiteness
  (`sofic-stable-implies-residually-finite`). This yields unstable groups only among non-residually-finite
  ones (`literal-group-not-stable-in-finite-actions`). Dies at residual finiteness.
* **Kazhdan groups.** Becker--Lubotzky refute strict P-stability of infinite sofic Kazhdan groups through
  punctured finite actions. Those almost actions are flexibly repairable, so they are silent here (recalled
  as in `sl3z-is-stable-in-finite-actions`). Dies.
* **F2 x F2.** `rf-finite-action-instability-from-f2xf2` reduces this to
  `f2xf2-not-stable-in-finite-actions`, which would follow from `f2xf2-in-paunescu-class`. Open.
