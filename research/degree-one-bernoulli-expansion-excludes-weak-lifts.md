---
rg: 2
id: degree-one-bernoulli-expansion-excludes-weak-lifts
kind: claim
title: If the Bernoulli shift of a w-rigid group has degree-one cocycle expansion with finite abelian coefficients, no nonsplit central extension has a liftable action weakly contained in Bernoulli
distinct_from:
  central-bernoulli-lifts-force-splitting: that is the exact case, with no expansion hypothesis; this is the approximate case, which needs a quantitative degree-one input.
  bernoulli-maximizes-extension-class-norm: that reduces weakly Bernoulli lifts to positivity of the Bernoulli norm of one class; this proves that positivity for all classes from one degree-one property of the Bernoulli shift.
  gohla-thom-class-norm-drops-under-weak-containment: that bounds the norm below through a degree-two cosystolic inequality on finite actions; this uses degree-one expansion on the Bernoulli shift instead, and needs no finite quotients.
artifacts:
  - research/artifacts/weakly-bernoulli-lifts-degree-one-reduction-2026-09-13.md
---

**ESTABLISHED (unreviewed)** by `degree-one-bernoulli-expansion-excludes-weak-lifts-proof`.

**Setting.** `Gamma = <S | R>` is finitely presented and w-rigid, and `A` is finite abelian. Degree-one cocycle
expansion with rate `rho` (`rho(eps) -> 0`) means: every `c : S x [0,1]^Gamma -> A` whose relator sums are nonzero on
measure at most `eps` agrees, off measure `rho(eps)` on each generator, with an exact 1-cocycle
`Gamma x [0,1]^Gamma -> A`.

**Statement.** If `[0,1]^Gamma` has degree-one cocycle expansion with coefficients `A` and some rate, then:
- **Norm bound.** There is `eps_0 > 0` such that for every nonzero `alpha in H^2(Gamma, A)`, every measurable
  `b : S x [0,1]^Gamma -> A` has `delta b != alpha_0` on measure at least `eps_0` at some relator. So the Gohla--Thom
  Bernoulli norm of `alpha` is positive.
- **No weak lifts.** By `bernoulli-maximizes-extension-class-norm`, no free action lifted across a nonsplit central
  extension is weakly contained in Bernoulli shifts.

**Proof idea.** Take `d = b(x) - b(x')`, which is an approximate cocycle. Expansion gives an exact cocycle nearby. Popa
makes it `delta f + chi`. The spectral gap of Bernoulli shifts of non-amenable groups, applied on three copies, forces
`chi = 0` and separates `f`. Then `b` is close to `delta g` plus a constant cochain, and constants cannot
approximate `alpha_0` without equalling it.

**Consequence.** The open instance `deligne-triple-cover-no-weakly-bernoulli-liftable-action` follows from degree-one
expansion of the Bernoulli shift of `Sp_4(Z)` (or of `Gamma(3)`) with `Z/3` coefficients,
`bernoulli-shifts-have-degree-one-cocycle-expansion`.

**Model test.** Hypothesis side: for free groups expansion holds trivially (no 2-cells) and `H^2 = 0`, so the claim is
vacuous, as it must be. Conclusion side: over the Gohla--Thom lattices the conclusion holds independently
(`gohla-thom-lattices-no-weakly-bernoulli-liftable-action`).
