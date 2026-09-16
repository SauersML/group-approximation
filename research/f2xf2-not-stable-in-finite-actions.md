---
rg: 2
id: f2xf2-not-stable-in-finite-actions
kind: claim
title: F2 x F2 is not stable in finite actions
distinct_from:
  f2xf2-is-stable-in-finite-actions: that is the negation
  literal-group-not-stable-in-finite-actions: that group is sofic and not residually finite, so its instability is forced by sofic-stable-implies-residually-finite; F2 x F2 is residually finite and that mechanism gives nothing
  residually-finite-group-not-stable-in-finite-actions: that is existential over residually finite groups (Gohla--Thom Question 3.12); this fixes F2 x F2 and implies that one
---

**OPEN.** Some sofic approximation of `Γ = F_2 × F_2` has a limit action that is not weakly contained in the
family of finite `Γ`-actions.

`Γ` is residually finite, so this would answer Gohla--Thom Question 3.12 positively
(`rf-finite-action-instability-from-f2xf2`). It follows from the target `f2xf2-in-paunescu-class`
(`f2xf2-finite-action-instability-from-paunescu-class`).

## Attempts

* **Via soficity of all actions.** If every action of `Γ` is sofic, the transfer
  `stable-finite-actions-sofic-actions-weakly-finite` puts every action in the weak closure of finite
  actions, contradicting `f2xf2-lacks-kechris-property-md`. Live but conditional on an open target.
* **A known sofic witness.** One needs a sofic action outside the weak closure of finite actions. Every
  sofic action I could identify lies inside it (artifact R2; the first two items are recalled, not
  source-checked):
  * products of `F_2`-actions and their factors, since `F_2` has MD;
  * compact translation actions;
  * Bernoulli shifts, by Abért--Weiss as quoted in Gohla--Thom Remark 3.14.

  Dies.
* **Gaussian witnesses.** The Gaussian action of a representation not weakly contained in
  finite-dimensional representations is outside the weak closure. Whether it is sofic is open. A sofic
  one would prove this claim through the transfer. Stalls.
* **Hamming-level obstructions.** Ioana's instability results (arXiv:1909.00282 Theorem D;
  arXiv:2008.00554 Theorem 1.5) forbid Hamming corrections of particular sofic approximations. They exhibit
  no partition statistics that finite actions cannot reproduce. No transfer found.
* **Koopman heuristic.** A limit action in the weak closure has Koopman representation weakly contained in
  finite-image representations. So a sofic approximation whose limit Koopman representation escapes the
  Fell closure of finite-dimensional representations would suffice.
  * Those coefficients are ultralimits of coefficients of Hamming-approximate permutation representations.
  * I found no way to steer them outside that closure.

  Heuristic only; no obstruction either.
