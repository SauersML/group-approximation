---
rg: 2
id: games-qpcp-from-tensor-power-amplified-xx-zz
kind: route
title: Measure a tensor-power amplified XX+ZZ Hamiltonian through the Steane-coded low-degree-test protocol
target: quantum-games-pcp-for-qma
requires: []
artifacts:
  - research/artifacts/qpcp-landscape-sources-2026-09-12.md
---

**Dead.** Invalidated by `natarajan-vidick-games-pcp-amplification-error`.

The tempting argument (Natarajan--Vidick, arXiv:1801.03821). XX+ZZ Hamiltonians
are QMA-hard at inverse-polynomial gap. Amplify by a tensor power to a constant
gap in operator norm. Seven provers hold the Steane encoding of the ground state.
The quantum low-degree test forces honest X/Z tensor measurements, and the verifier
samples one Pauli term and measures its logical operator. The acceptance bias is
linear in the energy, so the constant gap becomes a constant game gap.

Why it fails. The acceptance bias is `<H>/(2||H||_(P,1))`, measured against the
Pauli 1-norm, not the operator norm. Tensor-power amplification keeps the operator
norm but multiplies the Pauli 1-norm exponentially in the power. After
renormalization the game gap is not constant. The corrected lemma
(arXiv:2403.13084v1, Section 4.3) bounds the output 1-norm by
`1+2((1+||H||_(P,1))/2)^k`, which stays bounded only for inputs of 1-norm at most
one. `pauli-norm-games-qpcp-needs-imperfect-completeness` shows such inputs are
in NP unless `p/q <= 2+sqrt2`.
