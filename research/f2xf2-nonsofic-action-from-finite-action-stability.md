---
rg: 2
id: f2xf2-nonsofic-action-from-finite-action-stability
kind: route
title: Stability in finite actions makes the profinite upgrade of an action outside the weak closure of finite actions a free nonsofic action
target: f2xf2-admits-nonsofic-action
requires:
  - f2xf2-is-stable-in-finite-actions
  - f2xf2-lacks-kechris-property-md
  - stable-finite-actions-sofic-actions-weakly-finite
artifacts:
  - research/artifacts/f2xf2-finite-action-stability-dichotomy-2026-09-16.md
---

Conditional route (artifact §5, Theorem C(1)). Let `Γ = F_2 × F_2`.

1. By `f2xf2-lacks-kechris-property-md` there is a p.m.p. action `a` on a standard space with `a ⊀ F(Γ)`.
2. `Γ` is residually finite: free groups are, and a nontrivial `(g, h)` survives in a finite quotient of one
   coordinate. So `Γ ↷ Γ̂` with Haar measure is free, and `Γ̂` is infinite, so the measure is nonatomic.
   Then `a × Γ̂` is a free p.m.p. action on a standard nonatomic space.
3. By `f2xf2-is-stable-in-finite-actions` and part 3 of `stable-finite-actions-sofic-actions-weakly-finite`,
   `a × Γ̂` is not sofic. ∎

Gohla--Thom Remark 3.16 say informally that `a` itself would be nonsofic under stability, without a written
proof. The free upgrade is what this target asks for.
