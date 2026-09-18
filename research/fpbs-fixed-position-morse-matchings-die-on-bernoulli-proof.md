---
rg: 2
id: fpbs-fixed-position-morse-matchings-die-on-bernoulli-proof
kind: route
title: Take the height sublevel sets of a well-founded cut, show they are almost invariant under P, and contradict the Kesten gap of Bernoulli restricted to <P>
target: fpbs-fixed-position-morse-matchings-die-on-bernoulli
requires:
  - kesten-amenable-stabilizer-uniform-gap
  - fpbs-bernoulli-morse-collapse-criterion
artifacts:
  - research/artifacts/fpbs/docs/fixed-position-cutting-spectral-obstruction.md
---

Written proof, given in full in Sections 1–3 of the artifact.

1. **Children.** For `M_A`, the children of the `s`-edge at `x` are the `s`-edges at `p.x`, for `p in P` with
   `p.x in A`. Since `s^2 != 1`, freeness makes edges determine points. So (M3) is (WF).
2. **Height.** `h(x)` is the longest `P`-chain in `A` from `x`. It is finite a.s. by König's lemma, because the tree
   is `|P|`-branching and has no infinite branch.
   - Put `X_k = W ∪ {h <= k}`, with `W = X \ A`.
   - Then `p.(X_k \ W) ⊆ X_(k-1)`.
   - Hence `mu(X_k) <= mu(X_(k-1)) + delta` and `mu(p.X_k Δ X_k) <= 2 delta`.
3. **Balanced level.** Assume `delta < 1/4`. Take the least `k` with `mu(X_k) >= 1/2`, so `mu(X_k) < 3/4`, and put
   `f = 1_(X_k) - mu(X_k)`.
   - `||f||^2 >= 3/16`.
   - Summing over `T = P ∪ P^-1` gives `sum over t in T of ||pi(t) f - f||^2 <= 4 |P| delta`.
4. **Gap on Bernoulli.**
   - Products of a real orthonormal basis of `L^2_0(Y)` over finite supports form a basis of `L^2_0(Y^Gamma)`.
   - `Lambda` permutes this basis, with stabilizers inside `F F^-1`, which is finite.
   - So `L^2_0 = ⊕ l^2(Lambda / K_j)` with each `K_j` finite.
   - `kesten-amenable-stabilizer-uniform-gap` (KAG2) gives `kappa = 2 |T| (1 - rho) >= 2 |P| (1 - rho)` on every
     summand, and the same bound holds on any factor, whose `L^2_0` is an invariant subspace.
5. **Conclusion.** `4 |P| delta >= (3/16) 2 |P| (1 - rho)`, so `delta >= 3(1 - rho)/32`.

The extension to actions weakly contained in Bernoulli (artifact, Remark 5) uses Kechris's weak-containment transfer
[K]. It is not part of this route's established core.
