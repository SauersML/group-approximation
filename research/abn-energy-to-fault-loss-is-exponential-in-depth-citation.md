---
rg: 2
id: abn-energy-to-fault-loss-is-exponential-in-depth-citation
kind: route
title: Import the ABN circuit-to-Hamiltonian soundness thresholds
target: abn-energy-to-fault-loss-is-exponential-in-depth
requires: []
artifacts:
  - research/artifacts/qpcp-syndrome-rounding-audit-2026-08-25.md
---

**Established by citation.**  Anurag Anshu, Nikolas P. Breuckmann and
Quynh T. Nguyen, *Circuit-to-Hamiltonian from tensor networks and fault
tolerance*, arXiv:2309.16475, published in Proceedings of the 56th Annual ACM
Symposium on Theory of Computing (STOC 2024), pp. 585--595.

The abstract states both thresholds in these words: "we show that any state
with energy density exponentially small in the circuit depth encodes a noisy
version of the quantum computation with adversarial noise.  We also show that
any 'combinatorial state' with energy density polynomially small in depth
encodes the quantum computation with adversarial noise.  This serves as
evidence that any state with energy density polynomially small in depth has a
similar property."

The applications the paper does claim are QMA-completeness of the local
Hamiltonian problem at **logarithmic** locality and BQP-hardness of
contracting injective tensor networks to additive error.  It discusses the
implication for the quantum PCP conjecture; it does not prove it.  This route
imports only the two threshold statements, at the strength the abstract
gives them, and the citation was checked against the arXiv record on
2026-08-25.
