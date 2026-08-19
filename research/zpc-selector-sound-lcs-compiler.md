---
rg: 2
id: zpc-selector-sound-lcs-compiler
kind: claim
title: Tailored ZPC control compiles to an LCS with perfect-completeness and perfect-strategy sound decoding
artifacts:
  - research/artifacts/compiler-lowering-hyperlinear-2026-08-18.md
distinct_from:
  zpc-readable-control-freezing-to-lcs: freezing seeks one invariant global readable fiber before compiling; this claim permits the compiler to retain and encode the readable control, provided perfect finite-dimensional solutions decode soundly.
  finite-linear-commutation-system-to-lcs: that is an exact syntax compiler for already-unconditional relations; this claim must first eliminate controlled branching without creating spurious finite-dimensional perfect solutions.
---

There is an effective transformation taking a finite tailored game `G` to a
finite binary LCS `L(G)` with the following two properties.

1. Every perfect ZPC-IRS strategy for `G` induces a perfect commuting-operator
   strategy for `L(G)`.
2. Every perfect finite-dimensional strategy for `L(G)` decodes to a perfect
   finite-dimensional strategy for `G`.

It is enough for the transformation to work on the fixed finite game supplied
by `perfect-zpc-irs-quantum-gap-game`.

The established `controlled-linear-predication-normal-form` lowers every
controlled branch relation to parity equations in gated involutions. The
remaining problem is selector soundness: the compiler must express enough of
the mutually-exclusive/exhaustive readable-branch semantics that a perfect
finite-dimensional LCS solution cannot satisfy incompatible branches or evade
all branches. `one-hot-selector-parity-barrier` shows that, once an edge has
three or more alternatives, commuting selector bits plus affine parity rows
alone cannot enforce this invariant.

## Attempts

- **Predicated SSA form.** Use the gated involutions `G_(a,i)` and link copies
  back to each original unreadable variable with `prod_a G_(a,i)=U_i`. This
  gives exact local completeness. The failed step is enforcing the projection
  partition on selector variables by LCS parity alone.
- **Binary decision DAG.** Keep the verifier's control flow as a binary DAG
  rather than flattening leaves into an `m`-way one-hot vector. Seek a local
  consistency gadget whose perfect representations force one path while still
  permitting the ZPC direct-sum strategy.
- **Noncommutative selector code.** Allow a small noncommuting gadget whose
  representation theory has exactly the required branch sectors; then attach
  the predicated parity equations to those sectors. Soundness must prove that
  any finite-dimensional perfect representation decomposes into valid tailored
  branches.
- **Verifier-specific specialization.** Extract the actual readable decision
  DAG of the fixed TailoredMIP witness and minimize it before designing a
  general gadget. The barrier only rules out the naive affine one-hot encoding,
  not a structured binary compiler.
