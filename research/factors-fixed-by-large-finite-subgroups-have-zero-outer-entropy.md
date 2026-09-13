---
rg: 2
id: factors-fixed-by-large-finite-subgroups-have-zero-outer-entropy
kind: claim
title: A factor on which finite subgroups of unbounded order act trivially has zero outer Rokhlin entropy
distinct_from:
  rokhlin-supremum-dichotomy-with-centralized-self-copies: that kills Rokhlin entropy using finite subgroups that commute with a subgroup of finite supremum; this kills only the information in a factor that the finite subgroups fix, and it needs no finite supremum and no commuting subgroup.
  weak-invariants-give-no-bernoulli-rokhlin-lower-bound: that says invariants constant on weak equivalence classes give no lower bound; this is a vanishing theorem for the outer entropy of kernel-fixed factors inside a free action.
artifacts:
  - research/artifacts/rokhlin-kernel-trivial-information-2026-09-12.md
---

**Theorem.** Let `W ↷ (X, mu)` be free, ergodic and p.m.p. Let `F` be a `W`-invariant sub-sigma-algebra
generated under `W` by a countable partition `beta ⊆ F` with `H(beta) < infinity`. Suppose `W` has finite
subgroups `T_n` with `|T_n| -> infinity`, each acting trivially on `F`. Then:
- the outer Rokhlin entropy of `F` is `0`;
- `h^Rok_W(X) = h^Rok_W(X | F)`.

**Proof idea.** Record `beta` only on a Borel transversal `M` of the `T_n`-orbits. Since `beta` is
`T_n`-invariant, the partition `{X \ M} ∪ (beta ∩ M)` still generates `F`, and its entropy is
`H(1/|T_n|) + H(beta)/|T_n|`. Seward's subadditivity gives the equality.

**Consequences** (Section 2 of the artifact).
- **Normal subgroups.** Let `N ◁ W` have finite subgroups of unbounded order. Joining a free ergodic
  `W`-action with a finite-entropy action of `W/N` never raises Rokhlin entropy.
- **Kun–Thom wreaths.** `Rad_sof(W)` is the fibre-even lamp group, which is locally finite with finite
  subgroups of unbounded order. So information on which the sofic radical acts trivially, which is the
  only information sofic methods see, has zero outer Rokhlin entropy in every free ergodic `W`-action.
  Any positive Rokhlin entropy lives in information on which the invisible lamps act nontrivially. This
  is the action-level form of the witness localization.

**Limits.**
- The uniform Bernoulli shift over `W` has no nontrivial factor fixed by the radical, so this does not
  decide `kun-thom-wreath-bernoulli-rokhlin-maximal`.
- It gives no lower bound and no zero-or-infinity dichotomy for `W`.

**ESTABLISHED** by [[factors-fixed-by-large-finite-subgroups-zero-outer-proof]].
