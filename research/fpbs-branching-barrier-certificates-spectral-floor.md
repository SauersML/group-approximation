---
rg: 2
id: fpbs-branching-barrier-certificates-spectral-floor
kind: claim
title: A barrier for a branching recursion whose child differences generate a nonamenable group with spectral gap has measure at least an explicit delta_*, so single-rule relation certificates cannot prove cost one for the Bernoulli shift of the ascending HNN overgroup of Gamma_mal
distinct_from:
  fpbs-mal-sprinkle-then-absorb-inert: that kills pay-then-absorb chains for Gamma_mal through Bowditch fineness of cluster graphs at a malnormal stage; this kills recursion certificates in the overgroup M, and in any group, through the Kesten gap of the child-difference group acting on the level sets of the longest D-free descent, with no malnormality or cycle count.
  fpbs-bernoulli-class-approximants-are-almost-ergodic: that reads the Bernoulli Kesten gap at two-piece statistics to get near-ergodicity of approximants; this feeds the same gap into a monotone recursion of level sets and gets a lower bound on barrier measure.
  fpbs-extension-routes-to-finite-cost-are-circular: that kills extension and coinduction routes at the descent along non-atomic fibres; this kills the direct route to C(s_M) = 1 through sparse sprinkling of the non-amenable generator, and its artifact §4 sharpens item 4 there, since s_M restricted to Gamma_mal is s_{Gamma_mal}.
  fpbs-normal-subgroup-bounded-cost-fixed-price-one: that asks for fixed price one from a normal subgroup of bounded cost; this is an obstruction to one natural certificate of cost one, in a group where the normal subgroup is Gamma_mal and the question is open.
artifacts:
  - research/artifacts/fpbs-branching-barrier-certificates-spectral-floor-2026-09-17.md
  - experiments/branching-barrier-2026-09-17/check.py
  - experiments/branching-barrier-2026-09-17/check.out
---

**Setting.**
- `Gamma` is countable and acts p.m.p. on `(X, mu)`, with Koopman action
  `(g f)(x) = f(g^{-1} x)`.
- `c_1, ..., c_k ∈ Gamma`. A forward path from `y` is
  `y, c_{i_1} y, c_{i_2} c_{i_1} y, ...`.
- A measurable `D` is a *barrier* if, for a.e. `y`, every infinite forward
  path from `y` meets `D`.
- `P` is a nonempty set of pairs `{i ≠ j}`, and `s_{ij} = c_i c_j^{-1}`.

**(GH).** Assume that for all real `f ∈ L^2_0`,

```text
sum_P || f - s_{ij} f ||^2 >= kappa || f ||^2   for some kappa > 0.
```

Put `eta = kappa / (2|P|)` and
`delta_*(eta) = (sqrt(4 + eta^2) - 2)/eta`, which is about `eta/4`.

**Claim.**

1. **(Theorem A)** Under (GH):
   - every barrier has `mu(D) >= delta_*(eta)`;
   - if `mu(D) = delta < delta_*`, the set of points with an infinite
     forward path avoiding `D` has measure at least
     `(1 + sqrt(1 - 4 delta/eta))/2 > 1/2`.
2. **(Lemma G)** (GH) holds with `kappa = |S|(1 - rho(L, S))` when:
   - `S = {s_{ij}^{±1} : {i,j} ∈ P}` generates a nonamenable group `L`;
   - the Koopman representation restricted to `L` on `L^2_0` is weakly
     contained in `lambda_L`.

   This holds for the Bernoulli shift `s_Gamma`, and for every action weakly
   contained in it.
3. **(Corollary B)** Let `M = < a, b, t | t a t^{-1} = a, t b t^{-1} = b a b^{-2} >`
   be the ascending HNN overgroup of `Gamma_mal`, and take
   `c_1 = b^{-1} t`, `c_2 = b^{-2} t`, `c_3 = a b^{-2} t`.
   - The differences include `b` and `a^{-1}`, which generate a free group
     of rank 2.
   - So in `s_M` every barrier has `mu(D) >= delta_*(1 - rho)`, where
     `rho = rho(F_2, {a^±, b^±}) < 1`.
   - With Kesten's value `rho = sqrt(3)/2` this bound is `0.03346`.

**Consequence.** Take a graphing of `R_{<a,t>}` of cost `1 + epsilon`, add
`b` on `D`, and recover the remaining `b`-edges from the defining relation
`b = t^{-1} b a b^{-2} t`. This certifies `C(s_M) <= 1 + mu(D)` whenever `D`
is a barrier (artifact Lemma 2.1). So no such single-rule certificate proves
`C(s_M) = 1`.

Here `C(s_M) = 1` is the fixed price of `M`, because `C(M) = 1` (artifact
§4). The kill stops exactly when several derivation rules are combined
(artifact §3). The escape is amenable child differences, as in `BS(1,n)`.

## Attempts

* **2026-09-17 (swarm-0917-w12-w12-fp-break).** Proved items 1–3; the proof
  is in the artifact.
  - The floor is not sharp. Independent site barriers `{x(e) < p}` show that
    the optimal barrier measure for `s_M` lies in `[0.0334, 2/3]`.
  - The forward graph is not a tree: `c_3 = c_1 b`. Theorem A does not use a
    tree.
