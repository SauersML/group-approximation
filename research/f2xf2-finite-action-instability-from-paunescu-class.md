---
rg: 2
id: f2xf2-finite-action-instability-from-paunescu-class
kind: route
title: If every action of F2 x F2 is sofic, an action outside the weak closure of finite actions shows F2 x F2 is not stable in finite actions
target: f2xf2-not-stable-in-finite-actions
requires:
  - f2xf2-in-paunescu-class
  - f2xf2-lacks-kechris-property-md
  - stable-finite-actions-sofic-actions-weakly-finite
artifacts:
  - research/artifacts/f2xf2-finite-action-stability-dichotomy-2026-09-16.md
---

Conditional route (artifact §5, Theorem C(2)). Let `Γ = F_2 × F_2`, and suppose every p.m.p. action of `Γ`
on a standard space is sofic (`f2xf2-in-paunescu-class`).

* If `Γ` were stable in finite actions, `stable-finite-actions-sofic-actions-weakly-finite` would put every
  such action in the weak closure of finite actions.
* That contradicts `f2xf2-lacks-kechris-property-md`. So `Γ` is not stable in finite actions. ∎

**The obstruction this records.** Any proof of `f2xf2-in-paunescu-class` also produces a residually finite
group that is not stable in finite actions (`rf-finite-action-instability-from-f2xf2`). That is Gohla--Thom
Question 3.12, recorded as open by Alekseev--Thom (arXiv:2512.15494v1, introduction). The target is
therefore at least as hard as that question.
