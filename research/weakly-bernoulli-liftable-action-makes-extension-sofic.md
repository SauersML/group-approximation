---
rg: 2
id: weakly-bernoulli-liftable-action-makes-extension-sofic
kind: claim
title: A liftable action weakly contained in Bernoulli makes a finite central extension of a finitely presented sofic group sofic, through torsors over every sofic approximation of the base
distinct_from:
  gohla-thom-stable-base-nonsofic-extension: that derives nonsoficity of the extension from stability of the base; this derives soficity of the extension from one liftable weakly Bernoulli action, with no stability hypothesis.
  bernoulli-maximizes-extension-class-norm: that characterizes when such a lift exists by a vanishing norm; this turns such a lift into permutation models of the extension.
artifacts:
  - research/artifacts/weakly-bernoulli-lifts-sofic-transfer-and-sp4-2026-09-13.md
---

**ESTABLISHED (unreviewed)** by `weakly-bernoulli-liftable-action-makes-extension-sofic-proof`.

Let `Gamma` be finitely presented and sofic, `A` finite abelian, and `1 -> A -> Gamma~ -> Gamma -> 1` central. Suppose
some free p.m.p. `Gamma`-action that is the `A`-quotient of a free `Gamma~`-action is weakly contained in `[0,1]^Gamma`.
Then `Gamma~` is sofic. For every sofic approximation `V_n` of `Gamma`, `Gamma~` has a sofic approximation on
`V_n x A` in which `A` translates the second factor.

**Consequence for Deligne's triple cover.** A liftable weakly Bernoulli action of `Sp_4(Z)` would prove
`deligne-triple-cover-is-sofic`, which is open. So nonsoficity of `E_3` would imply
`deligne-triple-cover-no-weakly-bernoulli-liftable-action`, and a counterexample to that instance is at least as hard
as soficity of `E_3`.

**Model test.** Hypothesis side: a split `Gamma x A` has the liftable weakly Bernoulli action `Bern x A`, and it is
sofic. Conclusion side: over the Gohla--Thom lattices, `gohla-thom-lattices-no-weakly-bernoulli-liftable-action`
excludes the hypothesis, consistent with Gohla--Thom's conditional nonsoficity.
