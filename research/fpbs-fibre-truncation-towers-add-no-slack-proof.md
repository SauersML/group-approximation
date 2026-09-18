---
rg: 2
id: fpbs-fibre-truncation-towers-add-no-slack-proof
kind: route
title: Lift the exploration of the truncated cluster to the group and embed large balls into the truncations
target: fpbs-fibre-truncation-towers-add-no-slack
requires: []
artifacts:
  - research/artifacts/fpbs-fibre-truncation-towers-2026-09-17.md
---

Details are in Sections 1 and 2 of the artifact.

**Lifted exploration (Lemma 1.1).** Let `phi : X -> Y` be a locally surjective
graph homomorphism, such as a covering map.

* Explore the cluster of `phi(o)` in `Y` breadth-first.
* When an edge `f` from an explored vertex `y` to an unexplored vertex is
  examined, read the Bernoulli state of a lift `f~` of `f` at the current lift
  `L(y)`. If it is open, lift the new vertex through the other endpoint of `f~`.
* Fill the unexamined edges with independent coins.

Distinct examined edges have distinct lifts. Each lift is read once, and the
choices are adaptive, so the field on `Y` is iid Bernoulli(`p`). The lift `L`
is injective, since `phi ∘ L = id`, and it maps the cluster of `phi(o)` into
the cluster of `o`. Hence:

* `|K^Y ∩ A| <= |K^X ∩ phi^(-1)(A)|` in the coupling;
* an infinite cluster in `Y` lifts to an infinite cluster in `X`.

For `phi : G -> G_k` and `A = pi_k(H)`, `phi^(-1)(A) = H H_k = H`. For
`G_(k') -> G_k`, `phi^(-1)(A) = pi_(k')(H)`. This gives items 1 and 3.

**Local embedding (Theorem 2.1(2)).**

* **Injectivity.** If `H_k ∩ B_Gamma(2R+2) = {1}`, then `pi_k` is injective on
  `B_G(o,R+1)` and on the edges of `B_G(o,R)`. Indeed, if
  `pi_k(e) = pi_k(e')` then `e' = h e` with `h in H_k ∩ B_Gamma(2R)`, so
  `h = 1`.
* **Push-forward.** The Bernoulli field of `G_k` on the image edges is iid, so
  open paths inside `B_G(o,R)` push forward. Since the chain is nested with
  trivial intersection, for all large `k`

  ```text
  P(#{h in H ∩ B_G(o,R) : o <-> h in B_G(o,R)} >= n) <= P(|K^(G_k)_o ∩ pi_k(H)| >= n).
  ```

* **Limit.** As `R -> infinity` the left side increases to
  `P(|K^G_o ∩ H| >= n)`. Together with item 1, the probabilities converge.
  The expectations are sums of these tails and are nondecreasing in `k`, so
  they converge by monotone convergence.
