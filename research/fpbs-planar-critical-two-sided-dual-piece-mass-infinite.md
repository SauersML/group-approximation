---
rg: 2
id: fpbs-planar-critical-two-sided-dual-piece-mass-infinite
kind: claim
title: On some surface-group tiling the critical dual pieces on the two sides of an axis have infinite two-sided mean mass, refuting the uniform chemical stretch claim
distinct_from:
  fpbs-planar-stretch-bounded-below-by-dual-piece-mass: that is the established inequality K_*(p_u+) >= h mu(p_u) - 1; this is the open assertion mu(p_u) = infinity, which through that inequality refutes (UCS)
  fpbs-uniform-chemical-stretch-above-pu: that is the universal positive stretch claim; this is a planar counterexample mechanism for it, and says nothing about p_c < p_u, which holds on these graphs
---

**OPEN.** Notation as in `fpbs-planar-stretch-bounded-below-by-dual-piece-mass`.

**Claim.** For some `g >= 2`, with `a` a standard generator,
`mu(p_u) = E_(p_u)[ y(e_0) ] = infinity`.

**Consequence.** By item 3 of the established inequality, (UCS) fails on
`Cay(Gamma_g,S)`. So `fpbs-uniform-chemical-stretch-above-pu` would be
REFUTED, and the route `fpbs-intrinsic-l2-rate-via-uniform-stretch` would be
dead in its worst-case form. On these graphs `p_c < p_u` holds anyway
(`fpbs-hyperbolic-tiling-dual-clusters-bounded-from-pu`), so the flagship
statement is unaffected. What fails is the proof mechanism.

**Structure.** Let `X_± = |P_±(e_0)|`, and let `A_±` be the number of edges of
`L` adjacent to a face of `P_±(e_0)`. Since `m_± <= A_±`,
`y(e_0) >= 1[e_0 closed] * min(X_+/A_+, X_-/A_-)`.

- At `p_u` the dual process is critical Bernoulli(`p_c(G†)`) on `G†`.
- `(X_+,A_+)` and `(X_-,A_-)` are functions of the states of the edges not on
  `L` in `H_+` and in `H_-`, which are disjoint sets. So they are independent,
  and independent of the state of `e_0`. The `m_±` also depend on states of
  `L`-edges, which is why `A_±` is used.
- Ignoring `A`, `E[min(X_+,X_-)] = sum_(s>=1) P(X_+ >= s) P(X_- >= s)`.

**Where it is marginal.**

- The critical dual cluster in the whole plane has tail `s^(-1/2)` under
  mean-field behaviour.
- If each half-plane-restricted piece has the same tail up to constants,
  `P(X_+ >= s) P(X_- >= s) ≍ 1/s`, and the sum diverges **logarithmically**.
- Hyperbolic half-planes contain whole tree-like branches, so there is no
  boundary suppression as in `Z^d` half-spaces. This is the heuristic reason for
  the same tail.
- The adjacency counts `A_±` should have bounded moments, since branches that
  leave `L` escape ballistically and rarely return. This is heuristic.
- Any loss of a power of `log s` in the lower tail, or a correlation between
  `A` and `X`, changes the verdict. So the claim is not settled by the available
  imports.
- **Prediction at `p_u+`.** The parameter `t > p_u` truncates the sum at the
  dual correlation volume. That gives `K_*(t) ≳ h log(1/(t - p_u))`.

**Needed inputs.**

- (i) Half-plane one-sided lower tails
  `P_(p_c(G†))(X_± >= s) >= c s^(-1/2)` on both sides.
- (ii) `P(A_± <= M | X_± >= s) >= c'` uniformly in `s`, for a fixed `M`.

Given both, independence of the two sides and of `e_0` gives
`P(y(e_0) >= s/M) >= (1-p_u) c^2 c'^2 / s`. Hence
`mu(p_u) >= (1/M) sum_(s>=1) P(y >= s/M) = infinity`.

## Attempts

1. **Whole-cluster lower tail (2026-09-17).** Try to get (i) from the
   universal lower bound on the critical cluster tail, using
   `|C†(f_+)| <= X_+ + X_- + (pieces glued across closed L-edges)`.
   **Where it dies:** the critical dual cluster may reach size `s` by crossing
   `L` many times through closed axis edges, with every single piece small. The
   whole-cluster tail therefore gives no one-sided half-plane tail without a
   bound on the number of crossings of `L`. Controlling those crossings is
   input (ii) again, so the attack is circular.
