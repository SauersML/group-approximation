---
rg: 2
id: hereditary-property-second-level-dichotomy
kind: claim
title: Every hereditary property with a finitely presented counterexample is Pi-zero-two hard on enumerated presentations, with no approximation structure assumed
artifacts:
  - GroupApproximation/Computability/HereditaryPropertySwitchCompleteness.lean
  - GroupApproximation/Computability/SoficRecognitionSecondLevel.lean
  - GroupApproximation/Computability/IsoInvariantSwitchHardness.lean
distinct_from:
  second-level-rice-theorem-for-local-approximation-properties: that assumes the property is defined by finite-table models, which is what lets a merely finitely generated counterexample be upgraded to a finitely presented seed and what gives the two-generator and fixed-ambient sharpenings; this is the bare switch statement, which needs the seed to be finitely presented but assumes nothing else, and it is the form that is machine-checked.
  arbitrary-forbidden-seed-hereditary-property-switch: that is the switch itself and its two isomorphism types; this is the recognition-theoretic reading, stated as the dichotomy that covers every property in the ledger.
---

ESTABLISHED, and machine-checked.

**Theorem.**  Let `P` be a property of groups that is invariant under
isomorphism.  Assume either

```text
(H)  P is hereditary (passes to subgroups),  or
(I)  P is only isomorphism-invariant,
```

and that `P` holds for the trivial group and fails for some finitely
presented group `D`.  Then, on standard enumerated presentation codes,

```text
P is Pi^0_2-hard   and   not-P is Sigma^0_2-hard,                    (HD1)
```

and on the switch family itself `P` is `Pi^0_2`-complete.  In case (H) the
statement is `SoficRecognitionSecondLevel.pi02Hard_of_hereditary`; in case
(I) it is `IsoInvariantSwitchHardness.enumeratedCodeProperty_pi02Hard`,
which suffices because the switch has only the two isomorphism types `1`
and `D`.

**Dichotomy reading.**  For any such `P`: either every finitely presented
group has `P` --- in which case, on the switch family, recognition is
trivial --- or recognition of `P` is `Pi^0_2`-hard on enumerated
presentations.  Nothing between the two is possible.  All the rows of
[[arithmetical-complexity-table-of-group-properties]] are instances:
soficity, LEF, operator-MF, hyperlinearity, weak and linear soficity,
residual finiteness, residual `p`-finiteness, amenability,
torsion-freeness and free-subgroup-freeness use (H); triviality,
finiteness, commutativity, perfectness and Kazhdan's property (T) use (I).

**What the approximation structure adds.**  Only two things, both real:
[[local-approximation-properties-are-marked-closed]] upgrades a *finitely
generated* counterexample to a finitely presented seed, which is what
makes the hypothesis of this theorem checkable for soficity and
hyperlinearity; and it supplies the two-generator and fixed-ambient
sharpenings through the bridge and the Higman embedding.
