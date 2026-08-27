---
rg: 2
id: abn-energy-to-fault-loss-is-exponential-in-depth
kind: claim
title: The ABN circuit-to-Hamiltonian gives adversarial-noise semantics only at depth-vanishing energy density
invalidates:
  - qpcp-gap-from-abn-energy-semantics
artifacts:
  - research/artifacts/qpcp-syndrome-rounding-audit-2026-08-25.md
distinct_from:
  bgv-adversarial-fault-tolerance: that is the fault-tolerance theorem about how many physical qudits an adversary may corrupt per time step; this is about the energy-density threshold at which a circuit-to-Hamiltonian map still certifies a noisy computation, and it names no corruption budget.
---

**ESTABLISHED BY CITATION.**  Anshu, Breuckmann and Nguyen map an arbitrary
quantum circuit to a local Hamiltonian using injective tensor networks with
parent Hamiltonians, avoiding the Feynman--Kitaev clock register.  Their
soundness statements are threshold statements, and both thresholds vanish
with the circuit depth:

- any state whose energy density is **exponentially small in the circuit
  depth** encodes a noisy version of the computation with adversarial noise;
- any **combinatorial state** whose energy density is **polynomially small in
  the depth** encodes the computation with adversarial noise.

The authors present the second as evidence for the first at polynomially
small density; neither is a statement at constant energy density.

Consequently the ABN semantics cannot by itself certify a constant-gap NO
instance: the hypothesis it needs is `Tr(H rho) = o(1)`, and the conclusion
wanted for `quantum-pcp-constant-gap-local-hamiltonian` must hold at
`Tr(H rho) = Omega(1)`.  The abstract recursion behind the exponential loss
is isolated as (BSR) in
`checkpointed-syndrome-recursion-kills-depth-loss`, which shows the loss is
not intrinsic once constant-horizon anchors exist.
