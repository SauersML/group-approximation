---
rg: 2
id: weakly-bernoulli-liftable-action-makes-extension-sofic-proof
kind: route
title: Run block-factor approximations of the lifting cocycle on i.i.d. labels over a sofic approximation of the base
target: weakly-bernoulli-liftable-action-makes-extension-sofic
requires:
  - bernoulli-maximizes-extension-class-norm
artifacts:
  - research/artifacts/weakly-bernoulli-lifts-sofic-transfer-and-sp4-2026-09-13.md
---

Section 8 of the artifact (Theorem S).
1. **The lift.** `Gamma~ = <S ∪ A | A, [a,s], r = a_r>`. By item 1 of `bernoulli-maximizes-extension-class-norm`, the
   lifted action is `T_s(y,t) = (sy, t + b_s(sy))` with each relator accumulating `a_r`.
2. **Block approximation.**
   - Weak containment in `Bern` gives partitions `b'_s` whose joint law over the finitely many suffix translates is
     `delta`-close to that of `(b_s)`.
   - So each relator fails with probability `<= eta = |A|^(|S||F|) delta`. Approximating the `b'_s` by block functions
     of radius `rho` costs another `eta`.
3. **Transfer.** Evaluate the block functions on i.i.d. labels at the good vertices of the sofic approximation. The
   failure law there is the Bernoulli law. Fix a labeling with failure density `<= 3 eta + o(1)`.
4. **Permutations.** On `V_n x A` set `tau(s)(v,t) = (sigma_n(s)v, t + b^n_s(sigma_n(s)v))`, with `A` translating. The
   relations of `A` and the commutators hold exactly, and the relations `r = a_r` hold off the failure density.
5. **Freeness.**
   - If the image of `w` in `Gamma` is nontrivial, the base permutation moves most points.
   - If the image is trivial, `w = a != 0`. On good balls with no failing relator, the van Kampen diagram of
     `w a^-1` shows that `tau(w)` translates by `a`.
6. **Diagonal.** Letting `eta -> 0` diagonally in `n` gives a sofic approximation.
