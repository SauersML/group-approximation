---
rg: 2
id: gohla-thom-lattices-no-weakly-bernoulli-liftable-action
kind: claim
title: Over the Gohla--Thom lattices in PSp_2d(Q_p), no action lifted across the Prasad--Deligne kernel is weakly contained in Bernoulli shifts or in finite actions
distinct_from:
  weakly-bernoulli-liftable-actions-force-virtual-splitting: that is the open claim over every w-rigid base; this proves it over one family of property (T) bases, the ones where a cosystolic inequality is known.
  gohla-thom-stable-base-nonsofic-extension: that is the conditional nonsoficity of the extension; this is the unconditional statement about actions that the same cohomological engine gives.
artifacts:
  - research/artifacts/weakly-bernoulli-lifts-extension-class-norm-2026-09-13.md
---

**ESTABLISHED (unreviewed)** by `gohla-thom-lattices-no-weakly-bernoulli-liftable-action-proof`.

Let `d >= 4`, let `p >= 5` be large enough for Gohla--Thom Theorem 2.10, and let `Gamma` be a torsionfree
finite-index subgroup of `G(Z[1/p])`, where `G` has type `C_d` and `G(Q_p) ≅ Sp_2d(Q_p)` (their Section 3.4). Let
`1 -> A = Z/(p-1) -> Gamma~ -> Gamma -> 1` be the pullback of Prasad's universal central extension.
- **Norm bound.** There is `eps_0 > 0` such that every p.m.p. `Gamma`-action weakly contained in the family of finite
  `Gamma`-actions has `|||theta_*(alpha)||| >= eps_0`. This includes `[0,1]^Gamma` and the profinite completion.
- **No lifts.** No liftable free `Gamma`-action is weakly contained in a Bernoulli shift, or in the finite actions.
- **Hypotheses of the open claim.** `Gamma` has property (T), so it is w-rigid, and `Gamma~` is not virtually split.
  So `weakly-bernoulli-liftable-actions-force-virtual-splitting` holds over these bases.

**Credit.** For the single action `{0,1}^{Gamma~}/A`, the non-containment in finite actions is Gohla--Thom Remark
3.14. The general liftable case is their Theorem 3.4 combined with the same argument. The lane's contribution is
reading this as the Rokhlin-ascent obstruction over a (T) base, together with Bernoulli maximality
(`bernoulli-maximizes-extension-class-norm`).

**Consequence for Rokhlin ascent.** Over these bases, case (i) of `finite-kernel-rokhlin-ascent-from-weakly-minimal-lift`
never applies to the Prasad--Deligne extension. Only the Seward-conjecture case remains.

**Model test.**
- **Hypothesis side.** Every hypothesis is consumed. Residual finiteness and the cosystolic inequality bound the norm
  on finite actions. Non-residual-finiteness makes the class nonzero on every finite transitive action (GT Lemma
  2.15).
- **Split extension.** `Gamma x A` fails the hypothesis, and there `Bern x A` is a liftable Bernoulli action.
- **Conclusion side.** `{0,1}^{Gamma~}/A` is liftable and free, and it is not weakly contained in Bernoulli, which is
  consistent.
