---
rg: 2
id: fpbs-sphere-fibre-operator-iff-critical-fibre-l2
kind: claim
title: One critical sphere fibre operator below one is equivalent to a bounded critical fibre operator
distinct_from:
  fpbs-critical-sphere-fibre-operator-below-one: that is the open assertion that the one-radius condition holds over hyperbolic quotients; this is the unconditional equivalence of that condition with boundedness of the critical fibre operator over every quotient, which settles nothing about whether it holds.
  fpbs-rd-weighted-bubble-iff-sphere-fibre-operator-below-one: that shows over a rapid-decay quotient that the one-radius condition is equivalent to a polynomially weighted critical fibre bubble and to exponential l2 tail decay; this shows over every quotient, without rapid decay, that it is equivalent to boundedness of the critical fibre operator, and for amenable kernels to p_c < p_{2->2}.
  fpbs-sphere-cut-fibre-tails-decay-exponentially: that bootstraps one finite-radius operator norm to exponential decay of l2 fibre tails; this adds the converse, from a bounded critical fibre operator to exponential decay of complement operator norms.
  fpbs-tree-projected-sphere-bubble-l2-equivalence: that equivalence uses cut fibres and a sphere bubble on tree-projected generating sets; this uses fibre-saturated spheres and an operator norm over every quotient and every generating set.
  fpbs-amenable-kernel-l2-gap-forces-fibre-bubble: that derives only the unweighted critical fibre bubble from the L2 gap; this derives the one-radius operator condition, with explicit exponential decay of the complement norms.
artifacts:
  - research/artifacts/fpbs/docs/sphere-fibre-operator-is-critical-l2.md
---

**ESTABLISHED.** Let `Gamma` be finitely generated, `S` a finite symmetric
generating set, `H` any normal subgroup and `Q = Gamma/H`, with word length from
`pi(S)`. Put `sigma_p(q) = E_p|K_o ∩ Gamma_q|` and, for `f >= 0` on `Q`,
`N(f) = ||lambda_Q(f)||_{2->2}`. On `Cay(Gamma,S)` the following are equivalent:

* **(a)** `N(sigma_{p_c} 1_{S_Q(R_0)}) < 1` for some `R_0 >= 1`;
* **(b)** `N(sigma_{p_c}) < infinity`, so the critical fibre operator is bounded on `l2(Q)`;
* **(c)** for some `M < infinity`, `N(sigma_{p_c} 1_{|.| >= r}) <= M e^(-r/M)` for all `r >= 0`.

Explicitly, (b) gives (c) with `M = e N(sigma_{p_c})`. The three conditions
imply `p_c < p_{2->2}`. If `H` is amenable, they are equivalent to
`p_c < p_{2->2}`.

**Consequence.** Let `H` be amenable and the quotient have rapid decay. Then each
of the following is equivalent, graph by graph, to Hutchcroft's L2 boundedness
conjecture `p_c < p_{2->2}` (arXiv:1904.05804, Conjecture 1.3):
* `fpbs-critical-sphere-fibre-operator-below-one`;
* `fpbs-rd-quotient-weighted-critical-fibre-bubble`.

This covers surface groups times `Z`, Seifert-fibred groups, `hyperbolic x Z^k`
and central extensions. Neither premise is an easier target than critical L2
boundedness.

Proof: artifact Theorem A and Corollary B. The hard direction is Hutchcroft's
Proposition 2.4 of arXiv:1904.05804, run on fibre sums.
