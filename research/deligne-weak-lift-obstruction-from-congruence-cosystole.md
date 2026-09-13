---
rg: 2
id: deligne-weak-lift-obstruction-from-congruence-cosystole
kind: route
title: A congruence cosystolic bound makes the Bernoulli norm of the Deligne class positive, which excludes weakly Bernoulli lifts
target: deligne-triple-cover-no-weakly-bernoulli-liftable-action
requires:
  - deligne-class-congruence-cosystole-bounded-below
  - bernoulli-maximizes-extension-class-norm
  - gohla-thom-class-norm-drops-under-weak-containment
  - abert-weiss-free-actions-weakly-contain-bernoulli
artifacts:
  - research/artifacts/weakly-bernoulli-lifts-sofic-transfer-and-sp4-2026-09-13.md
---

Section 9 of the artifact.
1. **Reduce to `Gamma(3)`.** Restriction preserves liftability and weak containment, and `Bern(Sp_4(Z))|Gamma(3)` is a
   Bernoulli shift of `Gamma(3)`. So it suffices to exclude lifts over `Gamma(3)`.
2. **Profinite action.** Along the chain `Gamma(m_k)` of the hypothesis, the profinite action is free. By Abert--Weiss,
   `Bern ≺` it. It is contained in the ultraproduct of the finite actions `Gamma(3)/Gamma(m_k)`, as in the proof of
   `gohla-thom-lattices-no-weakly-bernoulli-liftable-action`.
3. **Norm bound.** By the Gohla--Thom chain of inequalities (item 1 of the import) and Shapiro's isometry,
   `|||theta^Bern(alpha)||| >= lim_𝒰 cosys(m_k) >= eps > 0`.
4. **Conclusion.** Item 4 of `bernoulli-maximizes-extension-class-norm`: no liftable free action is weakly contained in
   Bernoulli.
