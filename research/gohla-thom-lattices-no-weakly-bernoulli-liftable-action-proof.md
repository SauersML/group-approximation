---
rg: 2
id: gohla-thom-lattices-no-weakly-bernoulli-liftable-action-proof
kind: route
title: Cosystolic lower bound on finite actions, Bernoulli inside the profinite action, and liftable actions as zeros of the class
target: gohla-thom-lattices-no-weakly-bernoulli-liftable-action
requires:
  - gohla-thom-class-norm-drops-under-weak-containment
  - abert-weiss-free-actions-weakly-contain-bernoulli
  - bernoulli-maximizes-extension-class-norm
artifacts:
  - research/artifacts/weakly-bernoulli-lifts-extension-class-norm-2026-09-13.md
---

Section 5 of the artifact.
1. **Hypotheses.** `Gamma` is residually finite (Malcev) and of type F (GT Lemma 2.7). GT Theorem 2.10 gives the
   dimension-2 cosystolic inequality for finite transitive actions, since `d - 2 >= 2`. GT Theorem 3.18 gives a
   non-residually-finite `Gamma~`.
2. **Lower bound on finite actions.**
   - On a transitive action `Gamma/Λ`, the class is nonzero (GT Lemma 2.15), so its norm is at least `eps` by
     Definition 2.8(i).
   - A finite action is a disjoint union of transitive ones. Its cochain length is the weighted average over the
     pieces, and coboundaries act piecewise, so the bound `eps_0 = eps` holds on all finite actions.
3. **Weak containment.** By the proof of GT Corollary 2.14, `|||theta^Z||| >= eps_0` for every `Z` weakly contained in
   the finite actions.
4. **Bernoulli.**
   - `Bern ≺ Γ^` by Abert--Weiss, because translation on the profinite completion is free.
   - `M(Γ^)` is the closure of the union of the finite invariant algebras `P^{Gamma/Λ_n}` along a descending chain of
     finite-index normal subgroups with trivial intersection. It embeds equivariantly and measure-preservingly in
     their ultraproduct.
   - So `Bern` is weakly contained in the finite actions.
5. **Liftable actions.** They have norm 0 by item 1 of `bernoulli-maximizes-extension-class-norm`, so none is weakly
   contained in the finite actions.
6. **Property (T) and splitting.** Lattices in the higher-rank simple group `PSp_2d(Q_p)` have property (T). Splitting
   over a finite-index `Λ` would make `pi^-1(Λ) ≅ Λ x A` residually finite, and then `Gamma~` too, contradicting item 1.
