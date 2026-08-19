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

The established `controlled-linear-predication-normal-form` gives an exact
operator-level predicated normal form for each controlled branch relation. An
actual LCS compiler must additionally present enough consistency among the
gated copies and enough mutually-exclusive/exhaustive selector semantics that a
perfect finite-dimensional LCS solution cannot satisfy incompatible branches,
evade all branches, or assign unrelated operators to the gated copies.

Two established barriers delimit the purely affine approach.
`one-hot-selector-parity-barrier` rules out direct parity enforcement of a
three-or-more-way one-hot selector, while `affine-auxiliary-control-flow-barrier`
shows that adding arbitrarily many existential **commuting affine auxiliaries**
does not help: projections of affine solution sets stay affine, so neither
multiway one-hot control nor a path-activation bit `t=a AND b` can be encoded
that way.

## Attempts

- **Predicated SSA form.** Use the gated involutions `G_(a,i)` and link copies
  back to each original unreadable variable with `prod_a G_(a,i)=U_i`. This
  gives exact local completeness. The failed step is a sound LCS presentation
  of the gating/partition semantics; parity equations alone admit spurious
  representations.
- **Binary decision DAG with affine path bits — ruled out.** Replacing one
  multiway selector by binary choices does not solve the problem if a deeper
  path is represented by a classical auxiliary bit: path activation requires
  `t=a AND b`, which has no existential affine encoding. A useful binary DAG
  must avoid materializing conjunctions affinely or get the needed
  nonlinearity from operator structure.
- **Noncommutative selector code.** Allow a small noncommuting gadget whose
  representation theory has exactly the required branch sectors; then attach
  the predicated parity equations to those sectors. Soundness must prove that
  any finite-dimensional perfect representation decomposes into valid tailored
  branches.
- **Verifier-specific specialization.** Extract the actual readable decision
  structure of the fixed TailoredMIP witness and minimize it before designing a
  general gadget. The affine barriers rule out a whole compiler class but do
  not rule out a source-specific identity that eliminates branch conjunctions
  or a genuinely noncommutative gadget.
