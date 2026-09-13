---
rg: 2
id: quantum-games-pcp-for-qma
kind: claim
title: QMA has succinct MIP* protocols with efficient provers and a constant completeness-soundness gap (games quantum PCP)
artifacts:
  - research/artifacts/qpcp-landscape-sources-2026-09-12.md
  - research/artifacts/pauli-frustration-stabilizer-rounding-2026-09-12.md
distinct_from:
  quantum-pcp-constant-gap-local-hamiltonian: that is the Hamiltonian form; this is the games form, whose honest provers must be efficient given copies of the witness. MIP* = RE shows the games form is meaningless without that efficiency requirement.
---

**OPEN.** The conjecture of Fitzsimons--Vidick, in the form quoted by
Bergamaschi--Metger--Vidick--Zhang (arXiv:2510.01333v1, Section 1.1): there is an
MIP* protocol with `polylog(n)`-size questions and answers, a constant
completeness-soundness gap, and efficient honest provers, which decides all of
QMA. BMVZ state that the Hamiltonian form implies the games form, "considerably
harder to show than it is classically". No implication in either direction is
recorded as a route here. Natarajan--Nirkhe (arXiv:2403.13084v1) highlight that
MIP* = RE forces any connection between the two forms to restrict players to
efficient ones.

## Attempts

- **Natarajan--Vidick 2018: Steane-coded provers, quantum low-degree test, and a
  tensor-power amplified XX+ZZ Hamiltonian.** Dead. The amplification multiplies
  the Pauli 1-norm exponentially, so the gap after renormalization is not constant
  (`natarajan-vidick-games-pcp-amplification-error`). Separately, it relied on a
  low-degree soundness result that had a bug.
- **Bounded-norm inputs to the corrected lemma.** Partly excluded:
  `pauli-norm-games-qpcp-needs-imperfect-completeness` puts inputs of weight at
  most one with `p/q > 2+sqrt2` in NP. The window `1 < p/q <= 2+sqrt2` is open, and
  no QMA-hard family with bounded Pauli 1-norm in that window is known.
- **Streaming quantum PCP (BMVZ Theorem 7.4) with a succinct Pauli braiding test.**
  BMVZ believe this gives log-size questions and poly-size answers for QMA, with
  terms written as tensor products of 5-local Clifford projections. They report
  that it does not appear to help with succinct answers, which is where this
  attempt stops.
