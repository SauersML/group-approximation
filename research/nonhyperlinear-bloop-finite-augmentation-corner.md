---
rg: 2
id: nonhyperlinear-bloop-finite-augmentation-corner
kind: claim
title: Realize the fixed no-CE BCS in a full finite-subgroup augmentation corner without a normality constraint
distinct_from:
  nonhyperlinear-bloop-central-sign-corner: that imposes a central involution on the unknown host; this allows a nonnormal finite subgroup and its full augmentation complement.
  agent-leavitt-not-bcs-negative-root-corner: that fixes the binary-Leavitt Steinberg host and a particular noncentral root; this allows any explicitly constructed countable host and finite subgroup.
  signed-hecke-compatible-projection-atlas-for-nonce-bcs: that uses a selected irreducible type which a faithful finite-subgroup image may omit; this requires the full augmentation complement so every nontrivial subgroup image is detected.
artifacts:
  - research/artifacts/nonnormal-finite-augmentation-corner-endgame-2026-09-08.md
  - research/artifacts/noncentral-frobenius-negative-rational-matrix-corner-2026-09-08.md
  - research/artifacts/finite-augmentation-outside-normalizer-two-context-cell-2026-09-08.md
  - research/artifacts/finite-character-partial-rotation-cycle-algebra-2026-09-08.md
---

For the fixed finite BCS `B_loop` supplied by
`lin-explicit-fixed-bcs-gap-via-generic-conversion`, construct an
explicit countable group `G`, a specified embedded finite subgroup
`K!=1`, a named nonidentity `k in K`, and finite group-ring
expressions giving a unital star homomorphism

```text
Phi:A(B_loop) -> q_K C[G]q_K,
Phi(1)=q_K,              q_K=1-|K|^-1 sum_(h in K)h.
```

An explicit recursive presentation is permitted. Neither normality
of `K` nor centrality of its augmentation projection is required.
The map need not be injective or surjective and need not preserve
a specified source trace. The subgroup embedding and nontriviality
of `k` must be proved, along with every BCS relation for the finite
expressions. A selected finite-group type is not a substitute for
the specified corner unit.

## Attempts

- The existing noncentral torsion-corner theorem already settles
  the analytic implication for cyclic `K`. The general finite-
  subgroup endgame removes normality for all `K`, so the central
  involution required by the older gate is an optional restriction.
- `finite-translation-augmentation-corner-has-every-matrix-width`
  provides a full augmentation corner
  isomorphic to a matrix algebra and hence explicit local context
  partitions. Choosing a field size one modulo a desired matrix
  width removes the power-of-two limitation of finite involution
  packets. This constructs each local context, not the required
  equalities between different contexts in the final group ring.
- Equal full augmentation units force the finite translation
  subgroups of the local packets to coincide. Those packets and
  any literal corner-preserving group transporters all normalize
  that subgroup. To use the nonnormal option, some finite-support
  coefficients must involve elements outside this common normalizer.
- Putting all contexts in one finite matrix packet would give a
  finite-dimensional BCS model, contradicting the source gap.
  Independent finite amalgamations also leave the cross-context
  equalities unproved. Some finite-support algebraic expression
  outside these finite local models must enforce them exactly.
- `finite-augmentation-corner-has-outside-normalizer-contexts`
  constructs two noncommuting contexts with a shared proper atom and
  the same full augmentation unit. Their finite-support transport
  uses elements outside the subgroup normalizer and their supports
  fit in no finite subgroup. This resolves that local transport
  obstruction. The two contexts still generate a finite-dimensional
  algebra, and their wreath-product host has exact finite-window
  models, so it cannot realize the completed no-CE diagram.
- `strict-bcs-energy-in-augmentation-corner-kills-mf` supplies a
  separate sufficient endgame from one strict maximal-C-star energy
  inequality, without requiring an exact map. Its construction gate
  is `nonhyperlinear-bloop-strict-augmentation-energy`. That variant
  also excludes hyperlinear hosts; no inequality below its threshold
  has been constructed.
- `finite-character-rotation-cycles-have-exact-loop-algebra` handles
  additive rotations on finitely many orthogonal finite-character
  atoms. Their complete algebra is a matrix algebra over a twisted
  return-subgroup algebra, with an exact coset coefficient test for
  cycle closure. Closing all fundamental returns to scalars removes
  its infinite complexity; a successful infinite return algebra would
  already require a nonhyperlinear return subgroup. This does not
  supply the full BCS map. Overlapping noncommuting cuts remain
  outside the theorem and require additional exact identities.

No map of the displayed form for `B_loop` is currently supplied.
