---
rg: 2
id: bernoulli-maximizes-extension-class-norm
kind: claim
title: Among free actions the Bernoulli shift maximizes the norm of a central extension class, and a liftable action weakly contained in Bernoulli exists exactly when that norm is zero
distinct_from:
  weakly-bernoulli-liftable-actions-force-virtual-splitting: that is the open claim that such lifts exist only for virtually split extensions over w-rigid bases; this shows that, over any type-F base, the claim is equivalent to positivity of one number, the Bernoulli norm of the class.
  bernoulli-lifts-across-finite-kernels-force-virtual-splitting: that is Popa-type non-vanishing of the class on Bernoulli shifts in ordinary cohomology; this identifies the open claim with non-vanishing in the normed (reduced) sense, which Popa's argument does not reach.
artifacts:
  - research/artifacts/weakly-bernoulli-lifts-extension-class-norm-2026-09-13.md
---

**ESTABLISHED (unreviewed)** by `bernoulli-maximizes-extension-class-norm-proof`.

Let `Gamma` be of type F, `A` finite abelian, and `alpha in H^2(Gamma, A)` the class of a central extension
`1 -> A -> Gamma~ -> Gamma -> 1`. For a p.m.p. action `Z`, let `|||theta_*^Z(alpha)|||` be the Gohla--Thom norm of the
image of `alpha` in `H^2(Gamma, L^0(Z, A))`: the least measure-weighted Hamming size of a cocycle representative.
Call `Z` liftable if it is the `A`-quotient of a free p.m.p. `Gamma~`-action.
1. **Lifts are exact zeros.** A free `Z` is liftable iff `theta_*^Z(alpha) = 0`.
2. **Monotone.** `Z ≺ Z'` implies `|||theta^Z(alpha)||| >= |||theta^{Z'}(alpha)|||`.
3. **Bernoulli is maximal.** `|||theta^Z(alpha)||| <= |||theta^Bern(alpha)|||` for every free `Z`.
4. **Decision.** Some liftable free action is weakly contained in `[0,1]^Gamma` iff `|||theta^Bern(alpha)||| = 0`.
   Equivalently, no liftable free action is weakly contained in Bernoulli iff some free action has positive norm.

**Reading.** Popa gives `theta^Bern(alpha) != 0` over w-rigid bases for non-virtually-split classes. The open claim
`weakly-bernoulli-liftable-actions-force-virtual-splitting` is the statement that `theta^Bern(alpha)` stays away from
the closure of the coboundaries. Positive norm on any single free action suffices: the profinite completion
(cosystoles of finite covers), a homogeneous space, or `Bern` itself.

**Model test.** Hypothesis side: `Gamma = Z^2` with the mod-3 Heisenberg class. The class is nonzero, but it
vanishes on `3Z^2`, and an induced free liftable action is weakly equivalent to `Bern`, so the norm is 0. The
decision is about virtual splitting, not about `alpha != 0`. Conclusion side: over the Gohla--Thom lattices the
norm is positive (`gohla-thom-lattices-no-weakly-bernoulli-liftable-action`).
