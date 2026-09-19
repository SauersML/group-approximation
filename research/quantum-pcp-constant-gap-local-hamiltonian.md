---
rg: 2
id: quantum-pcp-constant-gap-local-hamiltonian
kind: claim
root: true
title: Constant-locality local Hamiltonian is QMA-hard at a constant relative promise gap
artifacts:
  - research/artifacts/qpcp-syndrome-rounding-audit-2026-08-25.md
distinct_from:
  classical-pcp-gap-is-not-tracial-pvm-gap: that is a no-go about transporting classical PCP soundness onto contextual tracial PVM assignments inside this repository's microstate program; this is the external complexity-theoretic conjecture about tensor-site local Hamiltonians, with a fixed finite-dimensional Hilbert space and a state-weighted energy.
  binary-pcp-coordinate-atlas-in-hs-microstates: that compiles a classical constant-query PCP into group words with normalized-HS energy; this is a statement about quantum local Hamiltonians and makes no reference to group approximation.
---

Fix a constant `k` and a constant local dimension.  For a `k`-local
Hamiltonian on `n` qudits,

```text
H = (1/m) sum_(a=1)^m h_a,        0 <= h_a <= I,               (QPCP1)
```

it is QMA-hard to distinguish

```text
lambda_min(H) <= a     from     lambda_min(H) >= b,            (QPCP2)
```

where `b - a >= Omega(1)` is independent of `n` and `m`.

This is the standard constant-locality form of the quantum PCP conjecture.
It is open; Bafna--Vyas (ECCC TR26-150, 19 August 2026) open with "The
quantum analogue of the PCP theorem for QMA remains wide open".  No node in
this region asserts otherwise.

The region below records one specific attack: obtain a **combinatorial** gap
from a locality-preserving amplifier, and convert it into an ordinary energy
gap by exactifying soft violations into commuting local fault syndromes at
linear cost.  The conversion step is
`combinatorial-gap-and-rounder-give-energy-gap`; the only prerequisite of
that step which is not already equivalent to this conjecture is
`local-syndrome-port-domination-at-each-gadget`.

## Attempts

- **Ordinary energy gap amplification.**  Killed for this target by
  `ordinary-gap-amplification-grows-locality`: the detectability-lemma
  amplification of Aharonov--Arad--Landau--Vazirani buys gap by enlarging the
  support of the terms, and the constant-locality promise here is exactly
  what that spends.
- **Circuit-to-Hamiltonian plus fault tolerance, used directly.**  Killed by
  `abn-energy-to-fault-loss-is-exponential-in-depth`: the Anshu--Breuckmann--Nguyen
  adversarial-noise semantics holds at energy density exponentially small in
  the circuit depth, and even the combinatorial-state version is only
  polynomially small.  Neither reaches a constant density.
- **Adversarial fault tolerance alone.**  Killed by
  `whole-time-slice-corruption-costs-inverse-depth`: on a depth-`D` circuit
  Hamiltonian a whole time layer is only a `Theta(1/D)` fraction of the
  terms, so a constant-density adversary can erase one outright, and no
  per-timestep guarantee tolerating `o(N)` corruptions survives that.
- **Bare rounder existence.**  Not an attack at all: by the converse half of
  `combinatorial-gap-and-rounder-give-energy-gap`, "a constant-cost rounder
  exists" is logically equivalent to this claim's conclusion.
