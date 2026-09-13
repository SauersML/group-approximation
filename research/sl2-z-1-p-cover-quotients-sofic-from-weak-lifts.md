---
rg: 2
id: sl2-z-1-p-cover-quotients-sofic-from-weak-lifts
kind: route
title: Weakly Bernoulli lifts over the finitely presented sofic base SL_2(Z[1/p]) make every finite universal-cover quotient sofic
target: sl2-z-1-p-universal-cover-quotients-are-sofic
requires:
  - deligne-sl2-z-1-p-weakly-bernoulli-lift
  - weakly-bernoulli-liftable-action-makes-extension-sofic
---

Complete argument, conditional on the open claim `deligne-sl2-z-1-p-weakly-bernoulli-lift`.

1. **The base is finitely presented.** By Serre's tree, `Q = SL_2(Z[1/p]) = SL_2(Z) *_(Γ_0(p)) SL_2(Z)`. This is an
   amalgam of two finitely presented groups over a finite-index, hence finitely generated, subgroup, so it is
   finitely presented.
2. **The base is sofic.** `Q` is finitely generated and linear, so it is residually finite by Mal'cev, and residually
   finite groups are sofic.
3. **The kernel.** `W_m = Γ~/mZ` is a central extension of `Q` by the finite abelian group `Z/m`, since `Z` is central
   in `Γ~`.
4. **The hypothesis.** `deligne-sl2-z-1-p-weakly-bernoulli-lift` supplies, for this `m`, a free p.m.p. `Q`-action that
   is the `Z/m`-quotient of a free `W_m`-action and is weakly contained in `[0,1]^Q`.
5. **Conclusion.** By `weakly-bernoulli-liftable-action-makes-extension-sofic`, `W_m` is sofic. ∎
