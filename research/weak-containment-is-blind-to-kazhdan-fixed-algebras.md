---
rg: 2
id: weak-containment-is-blind-to-kazhdan-fixed-algebras
kind: claim
title: Every action weakly contained in an action on which a Kazhdan subgroup is ergodic keeps that subgroup ergodic
invalidates: [mixing-nonsofic-action-via-weak-containment-of-kun-thom-action]
distinct_from:
  kazhdan-fixed-algebra-blind-to-subgroup-ergodic-actions: that shows the fixed diagonal algebra of a sofic embedding meets a subgroup-ergodic action only in the constants; this shows no action weakly contained in a subgroup-ergodic action, including factors of its ultrapowers, has a nonconstant fixed function for that subgroup
  abert-weiss-free-actions-weakly-contain-bernoulli: that imports the minimality of Bernoulli actions among free actions for weak containment; this is a rigidity statement for Kazhdan subgroups under weak containment
---

**ESTABLISHED.** Let `G` be a countable group, `Γ <= G` a subgroup with property (T), and
`G ↷ (Y, ν)` a p.m.p. action on which `Γ` acts ergodically. If `G ↷ (X, μ)` is weakly
contained in `G ↷ (Y, ν)` (Kechris; Alpeev arXiv:1706.01864, p. 5), then `Γ` acts
ergodically on `(X, μ)`. So `L^∞(X)^Γ = C`, and the conclusion of Kun--Thom Theorem C holds
for `X` trivially.

**Why it matters.** Nonsoficity moves up along weak containment: an action weakly
contained in a sofic action is sofic (Alpeev, p. 2: *"It is a folklore fact that an action
weakly contained in the sofic action is sofic itself."*). Weak containment does not
preserve mixing, so a mixing action weakly containing a Kun--Thom action would be a mixing
nonsofic action. This theorem rules that out whenever `Γ` is infinite: a mixing action
has `Γ` ergodic, so every action weakly contained in it is `Γ`-ergodic, while the
Kun--Thom actions have nonconstant `Γ`-fixed functions. Factors of ultrapowers of `Y` are
weakly contained in `Y`, so they are covered too.

This extends `kazhdan-fixed-algebra-blind-to-subgroup-ergodic-actions` from factors and
restrictions to the whole weak-containment closure.

Proof in `weak-containment-is-blind-to-kazhdan-fixed-algebras-proof`.
