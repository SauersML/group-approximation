---
rg: 2
id: dyadic-bruhat-tits-vertex-action-is-not-sofic
kind: claim
title: The dyadic PSL2 Bruhat--Tits vertex action is not sofic
distinct_from:
  dyadic-bruhat-tits-vertex-action-is-sofic: that is the negation
  psl2-bruhat-tits-action-soficity-forces-p-instability: that extracts noncorrectable permutation models of PSL2(Z[1/2]) from the positive side; this is the negative side itself, which would follow from flexible permutation stability
  sl3-regular-double-collapse-forces-nonsofic-vertex-action: that is the rank-two SL3 vertex action with a Kazhdan stabilizer; this is the rank-one PSL2 action, whose stabilizer is virtually free
---

**OPEN.** The coset action `PSL_2(Z[1/2]) ↷ PSL_2(Z[1/2])/PSL_2(Z)` is not sofic (GKP
Definition 2.1(5)).

**Equivalent forms.** By `dyadic-vertex-soficity-equals-frame-dynamics-soficity`, this is
equivalent to each of the following:
* nonsoficity of the uniquely ergodic frame dynamics `PSL_2(Z[1/2]) ↷ PSL_2(Q_2)/Λ`, for one
  (equivalently every) torsion-free cocompact `Λ`;
* nonexistence of approximate twin deep modular models.

**Hardness.** By `f2xf2-nonsofic-action-from-nonsofic-dyadic-vertex-action`, a proof of this claim
produces an essentially free nonsofic p.m.p. action of `F_2 × F_2`. That group is residually finite,
has the Haagerup property and contains no infinite Kazhdan subgroup. So this claim is at least as
hard as `f2xf2-admits-nonsofic-action`, and it is refuted by `f2xf2-in-paunescu-class`.

## Attempts

- **Kun--Thom compression.** Dead. The stabilizer `PSL_2(Z)` is virtually free, and the pair has
  no compressor. `nonamenable-relatively-kazhdan-infranormal-sofic-wreath` shows that even relative
  property (T) plus compression, without co-density, allows a sofic wreath.
- **Flexible permutation stability of `PSL_2(Z[1/2])`.** Live and conditional. By
  `codense-tau-coset-soficity-forces-permutation-instability`, stability would prove this claim.
  Stability is open; it is the permutation sibling of Dogon--Vigdorovich Question 1.4. By the
  hardness paragraph, such a stability theorem would also give a nonsofic action of `F_2 × F_2`.
- **Holonomy superrigidity on the frame face.** Dead as a direct transfer. Microstates of the frame
  dynamics carry return labels in `Λ`, which is a **free group**. The label superrigidity used
  against `SL_3(Z) ↷ SL_3(R)/Λ` has no analogue here.
  (`dyadic-homogeneous-quotient-admits-topological-microstates`, Attempts.)
- **Congruence models.** They are excluded with a uniform Selberg defect
  (`expanding-matchings-need-a-shared-stabilizer`). But that constrains the *format* of positive
  models; it does not exclude non-congruence ones.
