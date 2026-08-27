---
rg: 2
id: ordinary-gap-amplification-grows-locality-citation
kind: route
title: Import the detectability-lemma amplification and the July 2026 locality-preservation status
target: ordinary-gap-amplification-grows-locality
requires: []
artifacts:
  - research/artifacts/qpcp-syndrome-rounding-audit-2026-08-25.md
---

**Established by citation.**  Two sources, both checked on 2026-08-25.

1. Dorit Aharonov, Itai Arad, Zeph Landau and Umesh Vazirani, *The
   Detectability Lemma and Quantum Gap Amplification*, arXiv:0811.3412.  The
   abstract states the amplification "holds under the restriction that the
   interaction graph of the local Hamiltonian is an expander" and describes
   the result as "the quantum analogue of the first of the three main steps
   in Dinur's PCP proof".  The random-walk amplification it transports from
   Dinur's proof reads a `t`-step neighbourhood of the interaction graph as a
   single constraint, which is where the support of the amplified terms grows.

2. Simons Institute, Quantum Summer Cluster Final Workshop, 23 July 2026,
   *Gap Amplification for Local Hamiltonians with Combinatorial Soundness*,
   Quynh T. Nguyen (Harvard).  The abstract defines locality-preserving gap
   amplification as producing "a new instance with a larger promise gap,
   without increasing the locality of the Hamiltonian, and instead moderately
   increasing its local qudit dimension", says that "obtaining this kind of
   control over the locality during gap amplification is critical to the
   success of every known strategy for proving the classical PCP theorem",
   and offers "the first known viable template" for the quantum case.

The second source is the load-bearing one for the status half of the claim,
and it is a talk abstract rather than a refereed statement.  Nothing
downstream of this route uses more than the first source's construction shape
and the second source's own description of the prior state of the art.  See
`locality-preserving-constant-combinatorial-gap` for why the same talk is
**not** used to establish the amplifier itself.
