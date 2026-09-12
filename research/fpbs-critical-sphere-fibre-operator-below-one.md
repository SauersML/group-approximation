---
rg: 2
id: fpbs-critical-sphere-fibre-operator-below-one
kind: claim
title: Over a hyperbolic quotient some sphere-restricted critical fibre operator has norm below one
distinct_from:
  fpbs-rd-quotient-weighted-critical-fibre-bubble: that is the polynomially weighted critical fibre bubble summed over all radii; this is one operator norm at a single radius. They are equivalent by fpbs-rd-weighted-bubble-iff-sphere-fibre-operator-below-one, so this is the same premise at one scale.
  fpbs-tree-projected-critical-sphere-bubble-below-one: that asks for one critical sphere bubble below one on tree-projected generating sets; this asks for one sphere fibre operator norm below one on every generating set, where fibres are not cuts but fibre-saturated spheres are.
  fpbs-hyperbolic-quotient-uniform-fibre-bubble: that is the unweighted critical fibre bubble; this single-radius condition implies it with exponential decay of the tails, while the unweighted bubble gives no rate.
artifacts:
  - research/artifacts/fpbs/docs/sphere-cut-fibre-bootstrap.md
---

**OPEN.** Let `Gamma` be finitely generated with an infinite normal subgroup `H`
such that `Q = Gamma/H` is non-elementary word hyperbolic, and let `S` be a finite
symmetric generating set. Then some `R_0 >= 1` satisfies

```text
||lambda_Q(sigma_{p_c} 1_{S_Q(R_0)})||_{2->2}  <  1,
where sigma_p(q) = E_p|K_o ∩ Gamma_q|.
```

With rapid decay constants `C, D` of `Q`, sufficient explicit forms are
`b_{R_0}(p_c) < C^(-2) (1+R_0)^(-2D)`, or the same bound on the tail
`sum_{|q| >= R_0} sigma_{p_c}(q)^2`.

This claim gives:
* exponential decay of all critical fibre tails
  (`fpbs-sphere-cut-fibre-tails-decay-exponentially`);
* the weighted premise `fpbs-rd-quotient-weighted-critical-fibre-bubble`, and
  through it `p_c < p_u` on every Cayley graph in the class.

It is equivalent to that premise. Its value is that it is a statement about one
radius.

## Attempts

* **Mean-field profile.** For critical branching random walk the fibre occupation
  is the projected Green function. Its sphere bubbles decay exponentially, so the
  condition holds at large `R_0`. **Where it stops:** comparing with branching
  random walk is a triangle-type input.
* **From the unweighted bubble.** For amenable `H` the unweighted bubble is
  necessary for the L2 gap, but it only gives `T_R(p_c) -> 0`, with no rate. The
  condition needs the rate `(1+R)^(-2D)` at one radius. **Where it stops:** no rate
  mechanism.
* **Differential inequality.** Russo plus BK bound the growth of the sphere
  operator norm through `||S_p||`. **Where it dies:** the L2 barrier again.
* **Necessary rate.** The decay exponent `-(log theta)/R_0` is at most the volume
  entropy `h(Q)`, since otherwise `chi_{p_c}` would be finite. This is consistent
  with hyperbolic `Q`. It shows the condition must fail for quotients of
  subexponential growth, as it should.
* **Geodesic prefixes (heuristic).** In a `delta`-hyperbolic quotient the
  sphere-cut sum is dominated by `q'` near a geodesic prefix of `q` whenever
  `sigma_{p_c}` decays pointwise. **Where it stops:** that pointwise decay is the
  missing input.
