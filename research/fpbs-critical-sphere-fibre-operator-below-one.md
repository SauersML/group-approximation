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
  - research/artifacts/fpbs/docs/sphere-fibre-operator-is-critical-l2.md
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

It is not easier than critical L2 boundedness. By
`fpbs-sphere-fibre-operator-iff-critical-fibre-l2`, on each Cayley graph the
condition is equivalent to boundedness of `lambda_Q(sigma_{p_c})` on `l2(Q)`.
For amenable `H` it is equivalent to `p_c < p_{2->2}`, Hutchcroft's L2
boundedness conjecture on that graph.

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
* **Equivalence with critical L2 boundedness (2026-09-12).** Hutchcroft's
  averaged complement argument (arXiv:1904.05804, Proposition 2.4) runs on fibre
  sums. With the sphere cut it gives
  `fpbs-sphere-fibre-operator-iff-critical-fibre-l2`: the condition holds iff the
  critical fibre operator is bounded, and then complement norms decay
  exponentially. **Where it stops:** this is a reformulation, not a proof. For
  surface groups times `Z` and Seifert-fibred groups the claim is the L2
  boundedness conjecture on each Cayley graph.
* **Walk counting.** If `p_c |S| rho < 1`, where `rho` is the spectral radius of
  the image of the uniform measure on `S`, then
  `||lambda_Q(sigma_{p_c})|| <= (1 - p_c |S| rho)^(-1)` and the claim holds
  (artifact `sphere-fibre-operator-is-critical-l2.md`, Proposition C). **Where it
  stops:** nothing forces that inequality on a general generating set.
* **Single-kernel inequalities.** A kernel on `F_2 x Z` has all of these properties:
  * `tau(o,o) = 1`, and it is symmetric;
  * it satisfies Harris–FKG and the BK sphere cut at every radius;
  * it has infinite total mass and a finite fibre bubble.

  Yet its sphere fibre operator norm is at least 4 at every radius (artifact
  Proposition D). **Where it dies:** no argument that uses only those properties of
  `tau_{p_c}` can give the claim. A proof must use the `p`-dependence (Russo's
  formula, the susceptibility exponent) or new geometry.
* **Horofunction tilting (Hutchcroft's nonunimodular method).** Pulled-back
  horoballs are cuts, and crossing probabilities minimized over normalized
  horofunctions are supermultiplicative. **Where it dies:** the level-preserving
  elements of `Q` fix a boundary point, so the worst and best directions cannot be
  compared. Also, the `nu`-averaged half tilt is at most `||lambda_Q(sigma_p)||`,
  the wrong direction for a Schur test (artifact Section 5).
