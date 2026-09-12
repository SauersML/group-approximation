---
rg: 2
id: ordinary-gap-amplification-grows-locality
kind: claim
title: Known quantum energy gap amplification buys gap by enlarging the support of the terms
invalidates:
  - qpcp-gap-from-ordinary-energy-amplification
artifacts:
  - research/artifacts/qpcp-syndrome-rounding-audit-2026-08-25.md
---

**ESTABLISHED BY CITATION.**  The detectability-lemma amplification of
Aharonov, Arad, Landau and Vazirani is the quantum analogue of the first of
the three steps of Dinur's PCP proof: it amplifies the promise gap of a local
Hamiltonian whose interaction graph is an expander, by a random-walk
construction whose amplified terms are supported on `t`-neighbourhoods of
that graph.  The locality of the output therefore grows with the
amplification parameter, and driving an inverse-polynomial gap to a constant
one drives the locality to `omega(1)`.

That this remained the state of the art through July 2026 is recorded by the
Simons Institute abstract for *Gap Amplification for Local Hamiltonians with
Combinatorial Soundness*: locality-preserving gap amplification is described
there as one of the classical primitives with "no obvious quantum analogue",
and the talk offers "the first known viable template" for it.

So an attack on `quantum-pcp-constant-gap-local-hamiltonian` which reaches a
constant gap by ordinary energy amplification has, at that moment, given up
the constant-locality promise which is the whole content of the conjecture.
This is a statement about the published amplification primitives, not a
theorem that no locality-preserving energy amplification can exist.
