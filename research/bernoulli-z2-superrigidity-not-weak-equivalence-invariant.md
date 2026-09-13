---
rg: 2
id: bernoulli-z2-superrigidity-not-weak-equivalence-invariant
kind: claim
title: Z/2-cocycle superrigidity of a Bernoulli shift is not an invariant of weak equivalence
distinct_from:
  popa-bernoulli-cocycle-superrigidity: that is superrigidity for the Bernoulli shift itself; this shows a free action weakly equivalent to that shift can fail it.
  z2-by-f3-bernoulli-lacks-degree-one-cocycle-expansion: that is the quantitative failure of degree-one expansion on the Bernoulli shift; this is its qualitative form on an action in the same weak equivalence class.
artifacts:
  - research/artifacts/bernoulli-degree-one-expansion-amenable-seam-2026-09-13.md
---

**ESTABLISHED (unreviewed)** by `bernoulli-z2-superrigidity-not-weak-equivalence-invariant-proof`.

Let `Gamma = Z^2 x| F_3` be the w-rigid group of `z2-by-f3-bernoulli-lacks-degree-one-cocycle-expansion`,
with Bernoulli shift `X = [0,1]^Gamma`.
- **Rigid side.** Every measurable cocycle `Gamma x X -> Z/2` is cohomologous to a homomorphism.
- **Flexible side.** There is a free p.m.p. action `Gamma ↷ Y`, weakly equivalent to `X`, with a measurable cocycle
  `w : Gamma x Y -> Z/2` that is not cohomologous to any homomorphism.

**Why it matters.** Weak equivalence controls all finitary approximate structure, and superrigidity is not
finitary. The obstruction is an ultrapower eigenfunction of the amenable rigid subgroup `Z^2`. The failure of
degree-one expansion for `Sp_4(Z)`, if it happens, would have to come from a different mechanism, since `Sp_4(Z)`
has (T) and no amenable HNN seams.

**Model test.**
- **Hypothesis side.** For `Y = X` the rigid side holds (Popa), so `Y` must be a genuinely new member of the class.
  It is not a factor of `X`: a cocycle on a factor pulls back to `X`, where it is cohomologous to a homomorphism, and
  its restriction to `Z^2 x| F_2` would then contradict the spectral gap estimate.
- **Conclusion side.** `w` restricts on `Z^2 x| F_2` to the character `chi`, which does not extend to `Gamma`.
