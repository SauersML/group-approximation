---
rg: 2
id: qpcp-gap-from-abn-energy-semantics
kind: route
title: Read a constant energy gap off the ABN adversarial-noise semantics
target: quantum-pcp-constant-gap-local-hamiltonian
requires: []
artifacts:
  - research/artifacts/qpcp-syndrome-rounding-audit-2026-08-25.md
---

**Dead.**  Invalidated by
`abn-energy-to-fault-loss-is-exponential-in-depth`.

The tempting argument.  The Anshu--Breuckmann--Nguyen circuit-to-Hamiltonian
map already certifies that a low-energy state encodes a noisy run of the
computation under adversarial noise.  In a NO instance no such run accepts;
therefore no low-energy state exists; therefore the ground energy is bounded
below.

Why it fails.  The threshold is not constant.  Their adversarial-noise
semantics is stated for energy density **exponentially small in the circuit
depth**, and even the combinatorial-state version is stated at density
polynomially small in the depth.  A NO-instance floor of `Omega(1)` needs the
implication at `Tr(H rho) = Omega(1)`, and the cited theorems say nothing
there.  Deleting the input Hamiltonian does not help: their backward
propagation certifies Bell and fault coordinates throughout each light cone,
so the depth-vanishing threshold is not an artefact of input certification.

The abstract recursion behind the loss is (BSR) in
`checkpointed-syndrome-recursion-kills-depth-loss`, which shows the `L^D` is
removable once constant-spacing anchors exist.  That repair is the live route
`local-ports-from-checkpointed-anchors`, not this one.
