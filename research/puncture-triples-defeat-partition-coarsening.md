---
rg: 2
id: puncture-triples-defeat-partition-coarsening
kind: claim
title: Transposition triples on degree-one views keep oblivious completeness 1 - O(p^-l) yet push a unique verifier's value to r/(2r-1) while every partition coarsening keeps value 1
distinct_from:
  low-degree-view-collapse-survives-non-affine-sigma: that is the refuted statement that low-degree views with arbitrary bijections collapse to Can_part; this is the explicit counterexample family.
  affine-view-verifiers-collapse-up-to-puncture-cost: that is the corrected positive statement (affine views, arbitrary sigma, loss bounded by the puncture cost kappa, which pointwise completeness bounds by r eps); this shows that without a pointwise hypothesis kappa can be a constant.
  dummy-padding-cannot-beat-the-random-guessing-floor: that pads the alphabet with dummy labels in a 2-to-1 wrapper; this forbids two genuine labels per view through permutation constraints inside a unique verifier.
  unique-constraints-orient-at-most-half-of-a-fiber: that is the perfect-completeness injectivity wall; here completeness is 1 - O(p^-l) and the phenomenon is soundness beyond any coarsening.
artifacts:
  - experiments/puncture-triples-2026-09-17/check_puncture_triples.py
---

**ESTABLISHED.** Use the model of `low-degree-view-unique-verifiers-collapse`
(outer linear game `Phi`, output vertices with views `rho_w`, triples
`(w, w', sigma)` with arbitrary bijections `sigma`, oblivious completeness over a
uniform `h in H_e`, exact triples, `Can_part`).

**Family.** Fix a prime `p`, `l >= 2`, `2 <= r <= p^l - 1`, and put
`alpha = (r-1)/(2r-1)`. Identify `F_(p^l)` with `F_p^l`.

* *Outer game* `Phi_(l,r)`: two vertices `a, b`, `A_a = A_b = F_(p^l)`, and `r`
  edges of weight `1/r`, with `H_i = { (x, lambda_i x) }` for distinct nonzero
  `lambda_1, ..., lambda_r`. Each `H_i` is a linear subspace with both
  projections onto, so `Phi` is a linear outer game (a homogeneous linear unique
  game).
* *Verifier* `V_(l,r)`: output vertices `w_a, w_b` with identity views
  (`k = l`, degree `1`). On every edge `i`, `tau_i` puts weight `1 - alpha` on the
  cross triple `(w_a, w_b, x -> lambda_i x)`, and weight `alpha/2` on each of the
  same-owner triples `(w_a, w_a, pi)` and `(w_b, w_b, pi)`, where `pi` is the
  transposition of the two labels `0` and `1`.
* *Twin* `V^0_(l,r)`: the same views, supports and weights, with `pi` replaced by
  the identity.

**Statement.**

1. `V` has oblivious completeness `1 - 2 alpha p^(-l)`, so
   `eps = 2 alpha p^(-l) -> 0` as `l -> infinity`, while the view degree is `1`.
   Pointwise completeness fails: at `h = 0` honest labels are rejected with
   probability `alpha`.
2. `val(V(Phi)) = r/(2r-1)` (for example `2/3` at `r = 2`, and `-> 1/2` as `r`
   grows).
3. `val(Can_part(Phi, V)) = 1` and `val(V^0(Phi)) = 1`.

**Consequences.**

* `low-degree-view-collapse-survives-non-affine-sigma` is false. With `d = 1`
  and `gamma = 1/2`, the hypothesis `d <= (1 - gamma) log_p(1/eps)` holds for all
  `l >= 3`, but `val(V) = r/(2r-1) <= 2/3` while
  `(1 - o(1)) val(Can_part) - o(1) -> 1`.
* The failure is not a defect of the particular coarsening. `V` and `V^0` share
  the outer game, the views, the partitions, the triple supports and weights, and
  the compatible bijections `beta_t` (defined in
  `affine-view-verifiers-collapse-up-to-puncture-cost`). They differ only in
  `sigma` on two labels per same-owner triple, and they have values `r/(2r-1)` and
  `1`. So no functional of `(Phi, views, supports, weights, beta)` lower-bounds
  `val(V(Phi))` up to `o(1)` for oblivious-complete verifiers with arbitrary
  `sigma`, even at degree one.
* The invariant that separates `V` from `V^0` is the **puncture cost**: the weight
  of triples whose `sigma` departs from `beta_t` at the label a strategy uses. Here
  the forced near-optimal labeling of the coarsening is `F = 0`, and the
  punctures sit exactly on it.

This neither proves nor refutes UGC. The instance is a YES instance of `Phi`
(`x = 0` satisfies it); the verifier is simply not complete on that labeling,
which is why the corrected statement asks for pointwise completeness.

DERIVATION puncture-triples-defeat-partition-coarsening-proof
