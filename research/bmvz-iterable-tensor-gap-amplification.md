---
rg: 2
id: bmvz-iterable-tensor-gap-amplification
kind: claim
title: Derandomised tensor product amplification boosts layered Hamiltonian energy by sqrt(t/log t) per round at locality cost 2t, and iterates
artifacts:
  - research/artifacts/qpcp-dinur-iteration-architecture-2026-09-11.md
distinct_from:
  ordinary-gap-amplification-grows-locality: that records the detectability-lemma amplifier, which needs constant-locality input and cannot be iterated by itself; this is the iterable tensor-product amplifier with fixed layer weights and an explicit per-round factor, whose remaining obstacle is a composition step rather than iteration.
  kitaev-local-hamiltonian-is-qma-complete: that is the inverse-polynomial completeness theorem; this is an amplification procedure, with the QMA-complete layered starting family it needs.
---

**ESTABLISHED BY CITATION.** Bergamaschi--Metger--Vidick--Zhang,
*Derandomised tensor product gap amplification for quantum Hamiltonians*,
arXiv:2510.01333v1 (1 Oct 2025).

For a layered Hamiltonian `H` (Definition 1.6: `H=sum_chi w_chi H_chi` over `g`
layers, each an expectation of commuting projections, with
`omega_min=(min w_chi)^(-1)`), the derandomised amplification `H^(2t)`
(Definition 1.9) has the following properties.

- **Locality and size (Theorem 1.2).** `H^(2t)` is `2t k`-local with `d^(2t) m`
  clauses on `2t` copies.
- **Completeness (Proposition 4.1).** `lambda_min(H^(2t))<=2t lambda_min(H)`.
- **Soundness (proof of Corollary 6.13, (6.62) and (6.66)).**
  `lambda_min(H^(2t))>=min[(1/3)log t/t, eta sqrt(t/log t) lambda_min(H)]`, with
  `eta=1/(20 max{1+C_mu, omega_min})`, where `C_mu` depends only on the
  expander family and not on `t`.
- **Iteration (Section 7).** Layer count and `omega_min` are preserved; (7.5)
  iterates the bound.
- **Starting family (Section 8, Corollary 8.4, from ABN Claim 8.1).** There are
  QMA-complete 5-local projection Hamiltonians with YES energy `2^(-poly(n))`
  and NO energy at least `1/poly(n)`, split into `O(1)` equitable commuting
  layers, with `min_chi w_chi>=1/70`.

Consequences recorded by the source: iterated amplification to a constant gap
at locality `k p(n)^(O(1))` (Theorem 7.3), and a "streaming" quantum PCP with
`O(n)`-fold tensor products of `O(1)`-local projections (Theorem 7.4).

The source states the limitation verbatim: every quantisation of Dinur's
amplification so far is locality-increasing, "a significant obstacle to
applying the kinds of PCP composition theorems that make alphabet reduction
possible". The missing composition step is
`locality-reduction-with-amplifier-independent-loss`.
