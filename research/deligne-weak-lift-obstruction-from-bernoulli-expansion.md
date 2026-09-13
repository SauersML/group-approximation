---
rg: 2
id: deligne-weak-lift-obstruction-from-bernoulli-expansion
kind: route
title: Degree-one cocycle expansion of the Bernoulli shift of Sp_4(Z) excludes weakly Bernoulli lifts across Deligne's triple cover
target: deligne-triple-cover-no-weakly-bernoulli-liftable-action
requires:
  - bernoulli-shifts-have-degree-one-cocycle-expansion
  - degree-one-bernoulli-expansion-excludes-weak-lifts
  - bernoulli-maximizes-extension-class-norm
artifacts:
  - research/artifacts/weakly-bernoulli-lifts-degree-one-reduction-2026-09-13.md
---

1. **Hypotheses.** `Sp_4(Z)` is finitely presented and has property (T), so it is w-rigid. The Deligne class
   `alpha in H^2(Sp_4(Z), Z/3)` is nonzero, because `E_3` is not residually finite.
2. **Expansion.** `bernoulli-shifts-have-degree-one-cocycle-expansion` supplies degree-one expansion of `[0,1]^(Sp_4(Z))`
   with coefficients `Z/3`.
3. **Positive norm.** `degree-one-bernoulli-expansion-excludes-weak-lifts` makes the Bernoulli norm of `alpha`
   positive.
4. **Conclusion.** Item 4 of `bernoulli-maximizes-extension-class-norm` excludes liftable free actions weakly
   contained in Bernoulli.

No torsionfree reduction is needed: the argument uses only a finite presentation, not a finite classifying space.
